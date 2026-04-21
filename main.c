/*
 * Copyright (C) 2016 Unwired Devices <info@unwds.com>
 *               2017 Inria Chile
 *               2017 Inria
 *
 * This file is subject to the terms and conditions of the GNU Lesser
 * General Public License v2.1. See the file LICENSE in the top level
 * directory for more details.
 */

/**
 * @ingroup     tests
 * @{
 * @file
 * @brief       Test application for SX127X modem driver
 *
 * @author      Eugene P. <ep@unwds.com>
 * @author      José Ignacio Alamos <jose.alamos@inria.cl>
 * @author      Alexandre Abadie <alexandre.abadie@inria.fr>
 * @}
 */

#include <errno.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <inttypes.h>

#include "thread.h"
#include "shell.h"
//#include "shell_commands.h"
#include "ztimer.h"

#include "net/netdev.h"
#include "net/netdev/lora.h"
#include "net/lora.h"

#include "board.h"

#include "checksum/crc32.h"

#include "sx127x_internal.h"
#include "sx127x_params.h"
#include "sx127x_netdev.h"

#include "fmt.h"

#define SX127X_LORA_MSG_QUEUE   (16U)
#ifndef SX127X_STACKSIZE
#define SX127X_STACKSIZE        (THREAD_STACKSIZE_DEFAULT)
#endif

#define MSG_TYPE_ISR            (0x3456)
#define RELAY_DELAY_MS          (500U)
#define RELAY_SLEEP_MS           (50U)

static char stack[SX127X_STACKSIZE];
static char relay_stack[SX127X_STACKSIZE];
static kernel_pid_t _recv_pid;
static kernel_pid_t _relay_pid;

static char message[256];
static sx127x_t sx127x;

//////////////////////////////////////////
//////////// Global Variables ////////////
//////////////////////////////////////////

/* Messages counter when sending */
int messageCounter = 0;


/* Username */
#define NAME_LEN 4
char *username = NULL;

/* Channels */
#define MAX_CHANNELS     16
#define MAX_CHANNEL_LEN  32

static char subscribed_channels[MAX_CHANNELS][MAX_CHANNEL_LEN];
static int  channel_count = 0;

/* Storing user information */
typedef struct {
    char name[NAME_LEN];
    int last_msg_id;
    uint32_t last_seen;   // timestamp logique
} user_t;

/* Timestamp to track last user activity */
static uint32_t user_timestamp = 0;

/* Users management */
#define MAX_USERS 16
static user_t users[MAX_USERS];
static int user_count = 0;

/* Message */
typedef struct {
    char from[NAME_LEN + 1];
    char mode;
    char to[MAX_CHANNEL_LEN];
    int msg_id;
    int has_ttl;
    int ttl;
    char content[256];
} chat_msg_t;

typedef enum {
    RELAY_STATUS_RECEIVED = 0,
    RELAY_STATUS_PENDING,
    RELAY_STATUS_RELAYED,
    RELAY_STATUS_CANCELED,
} relay_status_t;

typedef struct {
    uint32_t crc; // CRC to check if message is already seen
    int8_t first_snr; // SNR of the first reception of the message, used to cancel relay if we receive the same message with better snr
    uint32_t last_seen; // Timestamp to know which is the oldest one
    relay_status_t relay_status;

    uint32_t time_to_send; // Timestamp to know when to send the message

    chat_msg_t msg; // Parsed message
} history_elt_t;

#define HIST_SIZE 32
static history_elt_t hist_buf[HIST_SIZE];
static int hist_first = 0;
static int hist_last = 0;
static uint32_t hist_timestamp = 0;

/* Relay */
static int8_t snr_threshold = -5;
//////////////////////////////////////////

/// Functions declaration
static int find_oldest_user(void);
static void update_user(const char *name, int msg_id);
int parse_chat_msg(const char *buf, size_t len, chat_msg_t *out);
static int hist_find_crc(uint32_t crc);
static uint32_t compute_crc(const chat_msg_t *parsed);
static void relay_process_pending(void);
static int build_chat_payload(const chat_msg_t *msg, bool include_ttl,
                              char *out, size_t out_len);

static bool time_reached(uint32_t now, uint32_t target)
{
    return ((int32_t)(now - target) >= 0);
}

static int build_chat_payload(const chat_msg_t *msg, bool include_ttl,
                              char *out, size_t out_len)
{
    if ((msg == NULL) || (out == NULL) || (out_len == 0)) {
        return -1;
    }

    int wrote;
    if (include_ttl) {
        wrote = snprintf(out, out_len, "%s%c%s:%d,%d:%s",
                         msg->from, msg->mode, msg->to,
                         msg->msg_id, msg->ttl, msg->content);
    }
    else {
        wrote = snprintf(out, out_len, "%s%c%s:%d:%s",
                         msg->from, msg->mode, msg->to,
                         msg->msg_id, msg->content);
    }

    if ((wrote < 0) || ((size_t)wrote >= out_len)) {
        return -1;
    }

    return 0;
}

static void schedule_relay_if_needed(const chat_msg_t *parsed, int8_t snr)
{
    if ((parsed == NULL) || !parsed->has_ttl || (parsed->ttl <= 0) || (strcmp(username,parsed->to)==0)){
        return;
    }

    int idx = hist_find_crc(compute_crc(parsed));
    if (idx < 0) {
        return;
    }

    history_elt_t *e = &hist_buf[idx];

    if (e->relay_status == RELAY_STATUS_RELAYED) {
        return;
    }

    e->relay_status = RELAY_STATUS_PENDING;
    e->first_snr = snr;
    e->time_to_send = ztimer_now(ZTIMER_MSEC) + RELAY_DELAY_MS;
}

static void relay_process_pending(void)
{
    uint32_t now = ztimer_now(ZTIMER_MSEC);

    for (int i = hist_first; i != hist_last; i = (i + 1) % HIST_SIZE) {
        history_elt_t *e = &hist_buf[i];
        chat_msg_t relay_msg;

        if (e->relay_status != RELAY_STATUS_PENDING) {
            continue;
        }

        if (!time_reached(now, e->time_to_send)) {
            continue;
        }

        relay_msg = e->msg;

        if (!relay_msg.has_ttl || (relay_msg.ttl <= 0)) {
            e->relay_status = RELAY_STATUS_CANCELED;
            continue;
        }

        relay_msg.ttl--;
        char relay_payload[256];

        if (build_chat_payload(&relay_msg, true, relay_payload, sizeof(relay_payload)) != 0) {
            e->relay_status = RELAY_STATUS_CANCELED;
            continue;
        }

        iolist_t iolist = {
            .iol_base = relay_payload,
            .iol_len = strlen(relay_payload) + 1,
        };

        netdev_t *netdev = &sx127x.netdev;
        if (netdev->driver->send(netdev, &iolist) == -ENOTSUP) {
            e->time_to_send = now + RELAY_SLEEP_MS;
            continue;
        }

        e->msg.ttl = relay_msg.ttl;
        e->relay_status = RELAY_STATUS_RELAYED;
        e->time_to_send = 0;
    }
}

static int hist_find_crc(uint32_t crc)
{
    int i = hist_first;

    while (i != hist_last) {
        if (hist_buf[i].crc == crc) {
            return i;
        }
        i = (i + 1) % HIST_SIZE;
    }

    return -1;
}

static uint32_t compute_crc(const chat_msg_t *parsed)
{
    char payload_no_ttl[sizeof(parsed->content) + MAX_CHANNEL_LEN + NAME_LEN + 24];

    if (parsed == NULL) {
        return 0;
    }

    if (build_chat_payload(parsed, false, payload_no_ttl, sizeof(payload_no_ttl)) != 0) {
        return 0;
    }

    return crc32(payload_no_ttl, strlen(payload_no_ttl));
}

int update_hist(int8_t snr, const chat_msg_t *parsed)
{
    uint32_t crc = compute_crc(parsed);
    int existing_idx = hist_find_crc(crc);

    if (existing_idx >= 0) {
        history_elt_t *e = &hist_buf[existing_idx];

        e->last_seen = ++hist_timestamp;

        if ((e->relay_status == RELAY_STATUS_PENDING) && (snr > e->first_snr) && (snr > snr_threshold)) {
            e->relay_status = RELAY_STATUS_CANCELED;
            e->time_to_send = 0;
        }

        return 0;
    }

    history_elt_t *e = &hist_buf[hist_last];

    e->crc = crc;

    e->msg = *parsed;

    e->first_snr = snr;
    e->last_seen = ++hist_timestamp;
    e->relay_status = RELAY_STATUS_RECEIVED;
    e->time_to_send = 0;

    hist_last = (hist_last + 1) % HIST_SIZE;
    if (hist_last == hist_first) {
        hist_first = (hist_first + 1) % HIST_SIZE;        
    }

    return 1;
}

int lora_setup_cmd(int argc, char **argv)
{

    if (argc < 4) {
        puts("usage: setup "
             "<bandwidth (125, 250, 500)> "
             "<spreading factor (7..12)> "
             "<code rate (5..8)>");
        return -1;
    }

    /* Check bandwidth value */
    int bw = atoi(argv[1]);
    uint8_t lora_bw;

    switch (bw) {
    case 125:
        puts("setup: setting 125KHz bandwidth");
        lora_bw = LORA_BW_125_KHZ;
        break;

    case 250:
        puts("setup: setting 250KHz bandwidth");
        lora_bw = LORA_BW_250_KHZ;
        break;

    case 500:
        puts("setup: setting 500KHz bandwidth");
        lora_bw = LORA_BW_500_KHZ;
        break;

    default:
        puts("[Error] setup: invalid bandwidth value given, "
             "only 125, 250 or 500 allowed.");
        return -1;
    }

    /* Check spreading factor value */
    uint8_t lora_sf = atoi(argv[2]);

    if (lora_sf < 7 || lora_sf > 12) {
        puts("[Error] setup: invalid spreading factor value given");
        return -1;
    }

    /* Check coding rate value */
    int cr = atoi(argv[3]);

    if (cr < 5 || cr > 8) {
        puts("[Error ]setup: invalid coding rate value given");
        return -1;
    }
    uint8_t lora_cr = (uint8_t)(cr - 4);

    /* Configure radio device */
    netdev_t *netdev = &sx127x.netdev;

    netdev->driver->set(netdev, NETOPT_BANDWIDTH,
                        &lora_bw, sizeof(lora_bw));
    netdev->driver->set(netdev, NETOPT_SPREADING_FACTOR,
                        &lora_sf, sizeof(lora_sf));
    netdev->driver->set(netdev, NETOPT_CODING_RATE,
                        &lora_cr, sizeof(lora_cr));

    puts("[Info] setup: configuration set with success");

    return 0;
}

int random_cmd(int argc, char **argv)
{
    (void)argc;
    (void)argv;

    netdev_t *netdev = &sx127x.netdev;
    uint32_t rand;

    netdev->driver->get(netdev, NETOPT_RANDOM, &rand, sizeof(rand));
    printf("random: number from sx127x: %u\n",
           (unsigned int)rand);

    /* reinit the transceiver to default values */
    sx127x_init_radio_settings(&sx127x);

    return 0;
}

int register_cmd(int argc, char **argv)
{
    if (argc < 2) {
        puts("usage: register <get | set>");
        return -1;
    }

    if (strstr(argv[1], "get") != NULL) {
        if (argc < 3) {
            puts("usage: register get <all | allinline | regnum>");
            return -1;
        }

        if (strcmp(argv[2], "all") == 0) {
            puts("- listing all registers -");
            uint8_t reg = 0, data = 0;
            /* Listing registers map */
            puts("Reg   0  1  2  3  4  5  6  7  8  9  A  B  C  D  E  F");
            for (unsigned i = 0; i <= 7; i++) {
                printf("0x%02X ", i << 4);

                for (unsigned j = 0; j <= 15; j++, reg++) {
                    data = sx127x_reg_read(&sx127x, reg);
                    printf("%02X ", data);
                }
                puts("");
            }
            puts("-done-");
            return 0;
        }
        else if (strcmp(argv[2], "allinline") == 0) {
            puts("- listing all registers in one line -");
            /* Listing registers map */
            for (uint16_t reg = 0; reg < 256; reg++) {
                printf("%02X ", sx127x_reg_read(&sx127x, (uint8_t)reg));
            }
            puts("- done -");
            return 0;
        }
        else {
            long int num = 0;
            /* Register number in hex */
            if (strstr(argv[2], "0x") != NULL) {
                num = strtol(argv[2], NULL, 16);
            }
            else {
                num = atoi(argv[2]);
            }

            if (num >= 0 && num <= 255) {
                printf("[regs] 0x%02X = 0x%02X\n",
                       (uint8_t)num,
                       sx127x_reg_read(&sx127x, (uint8_t)num));
            }
            else {
                puts("regs: invalid register number specified");
                return -1;
            }
        }
    }
    else if (strstr(argv[1], "set") != NULL) {
        if (argc < 4) {
            puts("usage: register set <regnum> <value>");
            return -1;
        }

        long num, val;

        /* Register number in hex */
        if (strstr(argv[2], "0x") != NULL) {
            num = strtol(argv[2], NULL, 16);
        }
        else {
            num = atoi(argv[2]);
        }

        /* Register value in hex */
        if (strstr(argv[3], "0x") != NULL) {
            val = strtol(argv[3], NULL, 16);
        }
        else {
            val = atoi(argv[3]);
        }

        sx127x_reg_write(&sx127x, (uint8_t)num, (uint8_t)val);
    }
    else {
        puts("usage: register get <all | allinline | regnum>");
        return -1;
    }

    return 0;
}

int send_cmd(int argc, char **argv)
{
    if (argc <= 1) {
        puts("usage: send <payload>");
        return -1;
    }

    printf("sending \"%s\" payload (%u bytes)\n",
           argv[1], (unsigned)strlen(argv[1]) + 1);

    iolist_t iolist = {
        .iol_base = argv[1],
        .iol_len = (strlen(argv[1]) + 1)
    };

    netdev_t *netdev = &sx127x.netdev;

    if (netdev->driver->send(netdev, &iolist) == -ENOTSUP) {
        puts("Cannot send: radio is still transmitting");
    }

    return 0;
}

int listen_cmd(int argc, char **argv)
{
    (void)argc;
    (void)argv;

    netdev_t *netdev = &sx127x.netdev;
    /* Switch to continuous listen mode */
    const netopt_enable_t single = false;

    netdev->driver->set(netdev, NETOPT_SINGLE_RECEIVE, &single, sizeof(single));
    const uint32_t timeout = 0;

    netdev->driver->set(netdev, NETOPT_RX_TIMEOUT, &timeout, sizeof(timeout));

    /* Switch to RX state */
    netopt_state_t state = NETOPT_STATE_RX;

    netdev->driver->set(netdev, NETOPT_STATE, &state, sizeof(state));

    printf("Listen mode set\n");

    return 0;
}

int syncword_cmd(int argc, char **argv)
{
    if (argc < 2) {
        puts("usage: syncword <get|set>");
        return -1;
    }

    netdev_t *netdev = &sx127x.netdev;
    uint8_t syncword;

    if (strstr(argv[1], "get") != NULL) {
        netdev->driver->get(netdev, NETOPT_SYNCWORD, &syncword,
                            sizeof(syncword));
        printf("Syncword: 0x%02x\n", syncword);
        return 0;
    }

    if (strstr(argv[1], "set") != NULL) {
        if (argc < 3) {
            puts("usage: syncword set <syncword>");
            return -1;
        }
        syncword = fmt_hex_byte(argv[2]);
        netdev->driver->set(netdev, NETOPT_SYNCWORD, &syncword,
                            sizeof(syncword));
        printf("Syncword set to %02x\n", syncword);
    }
    else {
        puts("usage: syncword <get|set>");
        return -1;
    }

    return 0;
}
int channel_cmd(int argc, char **argv)
{
    if (argc < 2) {
        puts("usage: channel <get|set>");
        return -1;
    }

    netdev_t *netdev = &sx127x.netdev;
    uint32_t chan;

    if (strstr(argv[1], "get") != NULL) {
        netdev->driver->get(netdev, NETOPT_CHANNEL_FREQUENCY, &chan,
                            sizeof(chan));
        printf("Channel: %i\n", (int)chan);
        return 0;
    }

    if (strstr(argv[1], "set") != NULL) {
        if (argc < 3) {
            puts("usage: channel set <channel>");
            return -1;
        }
        chan = atoi(argv[2]);
        netdev->driver->set(netdev, NETOPT_CHANNEL_FREQUENCY, &chan,
                            sizeof(chan));
        printf("New channel set\n");
    }
    else {
        puts("usage: channel <get|set>");
        return -1;
    }

    return 0;
}

int rx_timeout_cmd(int argc, char **argv)
{
    if (argc < 2) {
        puts("usage: channel <get|set>");
        return -1;
    }

    netdev_t *netdev = &sx127x.netdev;
    uint16_t rx_timeout;

    if (strstr(argv[1], "set") != NULL) {
        if (argc < 3) {
            puts("usage: rx_timeout set <rx_timeout>");
            return -1;
        }
        rx_timeout = atoi(argv[2]);
        netdev->driver->set(netdev, NETOPT_RX_SYMBOL_TIMEOUT, &rx_timeout,
                            sizeof(rx_timeout));
        printf("rx_timeout set to %i\n", rx_timeout);
    }
    else {
        puts("usage: rx_timeout set");
        return -1;
    }

    return 0;
}

int reset_cmd(int argc, char **argv)
{
    (void)argc;
    (void)argv;
    netdev_t *netdev = &sx127x.netdev;

    puts("resetting sx127x...");
    netopt_state_t state = NETOPT_STATE_RESET;

    netdev->driver->set(netdev, NETOPT_STATE, &state, sizeof(netopt_state_t));
    return 0;
}

static void _set_opt(netdev_t *netdev, netopt_t opt, bool val, char *str_help)
{
    netopt_enable_t en = val ? NETOPT_ENABLE : NETOPT_DISABLE;

    netdev->driver->set(netdev, opt, &en, sizeof(en));
    printf("Successfully ");
    if (val) {
        printf("enabled ");
    }
    else {
        printf("disabled ");
    }
    printf("%s\n", str_help);
}

int crc_cmd(int argc, char **argv)
{
    netdev_t *netdev = &sx127x.netdev;

    if (argc < 3 || strcmp(argv[1], "set") != 0) {
        printf("usage: %s set <1|0>\n", argv[0]);
        return 1;
    }

    int tmp = atoi(argv[2]);

    _set_opt(netdev, NETOPT_INTEGRITY_CHECK, tmp, "CRC check");
    return 0;
}

int implicit_cmd(int argc, char **argv)
{
    netdev_t *netdev = &sx127x.netdev;

    if (argc < 3 || strcmp(argv[1], "set") != 0) {
        printf("usage: %s set <1|0>\n", argv[0]);
        return 1;
    }

    int tmp = atoi(argv[2]);

    _set_opt(netdev, NETOPT_FIXED_HEADER, tmp, "implicit header");
    return 0;
}

int payload_cmd(int argc, char **argv)
{
    netdev_t *netdev = &sx127x.netdev;

    if (argc < 3 || strcmp(argv[1], "set") != 0) {
        printf("usage: %s set <payload length>\n", argv[0]);
        return 1;
    }

    uint16_t tmp = atoi(argv[2]);

    netdev->driver->set(netdev, NETOPT_PDU_SIZE, &tmp, sizeof(tmp));
    printf("Successfully set payload to %i\n", tmp);
    return 0;
}



static void _event_cb(netdev_t *dev, netdev_event_t event)
{
    if (event == NETDEV_EVENT_ISR) {
        msg_t msg;

        msg.type = MSG_TYPE_ISR;
        msg.content.ptr = dev;

        if (msg_send(&msg, _recv_pid) <= 0) {
            puts("gnrc_netdev: possibly lost interrupt.");
        }
    }
    else {
        size_t len;
        netdev_lora_rx_info_t packet_info;
        switch (event) {
        case NETDEV_EVENT_RX_STARTED:
            puts("Data reception started");
            break;

        case NETDEV_EVENT_RX_COMPLETE:
            len = dev->driver->recv(dev, NULL, 0, 0);
            dev->driver->recv(dev, message, len, &packet_info);
            printf("Received message: \"%s\" (%d bytes)\n", message, (int)len);

            chat_msg_t *parsed = malloc(sizeof(chat_msg_t));
            if (parsed == NULL) {
                printf("Failed to allocate memory for parsed message\n");
                break;
            }

            if (parse_chat_msg(message, len, parsed) != 0) {
                printf("Unknown message format\n");
                printf("{Payload: \"%s\" (%d bytes), RSSI: %i, SNR: %i, TOA: %" PRIu32 "}\n",
                    message, (int)len,
                    packet_info.rssi, (int)packet_info.snr,
                    sx127x_get_time_on_air((const sx127x_t *)dev, len));
                break;
            }

            int hist_added = update_hist((int8_t)packet_info.snr, parsed);
            if (!hist_added) {
                printf("Duplicate message ignored for history\n");
            }

            if (!parsed->has_ttl) {
                printf("Relay skipped: no TTL field");
            }
            else if (parsed->ttl <= 0) {
                printf("Relay skipped: TTL <= 0");
            }
            else if (hist_added) {
                // Here we have a ttl and its > 0
                schedule_relay_if_needed(parsed, (int8_t)packet_info.snr);
                printf("Relay pending in %u ms\n", (unsigned)RELAY_DELAY_MS);
            }

            if (parsed->mode == '@') {
                if (strcmp(username, parsed->to) == 0) {
                    printf("Private message received\n");
                    printf("@%s[%d] : %s\n", parsed->from, parsed->msg_id, parsed->content);
                }
                update_user(parsed->from, parsed->msg_id);
            }
            else { /* '#' */
                for (int i = 0; i < channel_count; i++) {
                    if (strcmp(subscribed_channels[i], parsed->to) == 0) {
                        printf("[CHANNEL #%s]@%s[%d] : %s\n",
                            parsed->to, parsed->from, parsed->msg_id, parsed->content);
                        update_user(parsed->from, parsed->msg_id);
                        break;
                    }
                }
            }
            free(parsed);
            break;
        case NETDEV_EVENT_TX_COMPLETE:
            sx127x_set_sleep(&sx127x);
            puts("Transmission completed");
            break;

        case NETDEV_EVENT_CAD_DONE:
            break;

        case NETDEV_EVENT_TX_TIMEOUT:
            sx127x_set_sleep(&sx127x);
            break;

        default:
            printf("Unexpected netdev event received: %d\n", event);
            break;
        }
    }
}

void *_recv_thread(void *arg)
{
    (void)arg;

    static msg_t _msg_q[SX127X_LORA_MSG_QUEUE];

    msg_init_queue(_msg_q, SX127X_LORA_MSG_QUEUE);

    while (1) {
        msg_t msg;
        msg_receive(&msg);
        if (msg.type == MSG_TYPE_ISR) {
            netdev_t *dev = msg.content.ptr;
            dev->driver->isr(dev);
        }
        else {
            puts("Unexpected msg type");
        }
    }
}

void *_relay_thread(void *arg)
{
    (void)arg;

    while (1) {
        relay_process_pending();
        ztimer_sleep(ZTIMER_MSEC, RELAY_SLEEP_MS);
    }
}


int init_sx1272_cmd(int argc, char **argv)
{
    (void)argc;
    (void)argv;
	    sx127x.params = sx127x_params[0];
	    netdev_t *netdev = &sx127x.netdev;

	    netdev->driver = &sx127x_driver;

        netdev->event_callback = _event_cb;

//        printf("%8x\n", (unsigned int)netdev->driver);
//        printf("%8x\n", (unsigned int)netdev->driver->init);

	    if (netdev->driver->init(netdev) < 0) {
	        puts("Failed to initialize SX127x device, exiting");
	        return 1;
	    }

	    _recv_pid = thread_create(stack, sizeof(stack), THREAD_PRIORITY_MAIN - 1,
	                              THREAD_CREATE_STACKTEST, _recv_thread, NULL,
	                              "recv_thread");

	    if (_recv_pid <= KERNEL_PID_UNDEF) {
	        puts("Creation of receiver thread failed");
	        return 1;
	    }

        _relay_pid = thread_create(relay_stack, sizeof(relay_stack), THREAD_PRIORITY_MAIN - 2,
                                   THREAD_CREATE_STACKTEST, _relay_thread, NULL,
                                   "relay_thread");

        if (_relay_pid <= KERNEL_PID_UNDEF) {
            puts("Creation of relay thread failed");
            return 1;
        }
        puts("5");

        return 0;
}



static int find_oldest_user(void)
{
    if (user_count == 0) {
        return -1;
    }

    int oldest = 0;
    for (int i = 1; i < user_count; i++) {
        if (users[i].last_seen < users[oldest].last_seen) {
            oldest = i;
        }
    }
    return oldest;
}

static void update_user(const char *name, int msg_id)
{
    user_timestamp++;

    /* utilisateur déjà connu */
    for (int i = 0; i < user_count; i++) {
        if (strcmp(users[i].name, name) == 0) {
            users[i].last_msg_id = msg_id;
            users[i].last_seen = user_timestamp;
            return;
        }
    }

    /* nouveau utilisateur */
    if (user_count < MAX_USERS) {
        strncpy(users[user_count].name, name, NAME_LEN - 1);
        users[user_count].name[NAME_LEN - 1] = '\0';
        users[user_count].last_msg_id = msg_id;
        users[user_count].last_seen = user_timestamp;
        user_count++;
    }
    else {
        /* tableau plein : remplacer plus ancien */
        int oldest = find_oldest_user();

        printf("User table full replacing %s\n", users[oldest].name);

        strncpy(users[oldest].name, name, NAME_LEN - 1);
        users[oldest].name[NAME_LEN - 1] = '\0';
        users[oldest].last_msg_id = msg_id;
        users[oldest].last_seen = user_timestamp;
    }
}

int users_cmd(int argc, char **argv)
{
    (void)argc;
    (void)argv;

    printf("Known users (%d):\n", user_count);

    for (int i = 0; i < user_count; i++) {
        printf("- %s (last msg id: %d)\n",
               users[i].name,
               users[i].last_msg_id);
    }

    return 0;
}




int set_username_cmd(int argc, char **argv)
{
    if (argc < 2) {
        printf("usage: %s <username>\n", argv[0]);
        return 1;
    }

    free(username);
    username = malloc(NAME_LEN+1);
    if (username == NULL) {
        printf("Failed to allocate memory for username\n");
        return 1;
    }
    username = strncpy(username, argv[1], NAME_LEN);
    username[NAME_LEN] = '\0';
    printf("Username set to: %s\n", username);
    return 0;
}

int msg_cmd(int argc, char **argv)
{
    if (argc < 4) {
        printf("usage: %s <@|#> <to> <message> [ttl]\n", argv[0]);
        return 1;
    }

    if (username == NULL) {
        printf("Username should be set before sending messages. Please set it first.\n");
        return 1;
    }

    const char *type = argv[1];
    const char *target = argv[2];
    const char *msg_text = argv[3];
    const int message_number = messageCounter++;
    int has_ttl = 0;
    int ttl = 0;

    if ((strcmp(type, "@") != 0) && (strcmp(type, "#") != 0)) {
        printf("usage: %s <@|#> <to> <message> [ttl]\n", argv[0]);
        return 1;
    }

    if (argc >= 5) {
        ttl = atoi(argv[4]);
        if (ttl < 0) {
            puts("ttl must be >= 0");
            return 1;
        }
        has_ttl = 1;
    }

    /* base: user + type + to + ':' + id + ':' + msg + '\0' */
    int payload_size = (int)strlen(username) + (int)strlen(type) + (int)strlen(target) +
                       (int)strlen(msg_text) + 4 + 10;
    if (has_ttl) {
        /* add ',' + ttl (up to 10 digits for int32) */
        payload_size += 1 + 10;
    }

    char *payload = malloc(payload_size);
    if (payload == NULL) {
        printf("Failed to allocate memory for payload\n");
        return 1;
    }

    if (has_ttl) {
        snprintf(payload, payload_size, "%s%s%s:%d,%d:%s",
                 username, type, target, message_number, ttl, msg_text);
    }
    else {
        snprintf(payload, payload_size, "%s%s%s:%d:%s",
                 username, type, target, message_number, msg_text);
    }

    printf("Sending: %s\n", payload);

    iolist_t iolist = {
        .iol_base = payload,
        .iol_len = (strlen(payload) + 1)
    };

    netdev_t *netdev = &sx127x.netdev;
    if (netdev->driver->send(netdev, &iolist) == -ENOTSUP) {
        puts("Cannot send: radio is still transmitting");
    }

    free(payload);
    return 0;
}

int subscribe_cmd(int argc, char **argv)
{
    if (argc < 2) {
        printf("usage: %s <channel>\n", argv[0]);
        return 1;
    }

    const char *channel = argv[1];

    /* vérifier si déjà abonné */
    for (int i = 0; i < channel_count; i++) {
        if (strcmp(subscribed_channels[i], channel) == 0) {
            printf("Already subscribed to #%s\n", channel);
            return 0;
        }
    }

    /* vérifier si la table est pleine */
    if (channel_count >= MAX_CHANNELS) {
        printf("Cannot subscribe: max %d channels reached\n", MAX_CHANNELS);
        return 1;
    }

    /* ajouter */
    strncpy(subscribed_channels[channel_count], channel, MAX_CHANNEL_LEN - 1);
    subscribed_channels[channel_count][MAX_CHANNEL_LEN - 1] = '\0';
    channel_count++;

    printf("Subscribed to #%s\n", channel);
    return 0;
}

int unsubscribe_cmd(int argc, char **argv)
{
    if (argc < 2) {
        printf("usage: %s <channel>\n", argv[0]);
        return 1;
    }

    const char *channel = argv[1];

    for (int i = 0; i < channel_count; i++) {
        if (strcmp(subscribed_channels[i], channel) == 0) {

            /* décaler les entrées suivantes vers la gauche */
            for (int j = i; j < channel_count - 1; j++) {
                strncpy(subscribed_channels[j], subscribed_channels[j + 1],
                        MAX_CHANNEL_LEN);
            }
            channel_count--;

            printf("Unsubscribed from #%s\n", channel);
            return 0;
        }
    }

    printf("Not subscribed to #%s\n", channel);
    return 1;
}

int print_hist(int argc, char **argv)
{
    (void)argc;
    (void)argv;

    int i = hist_first;
    if (hist_first == hist_last) {
        puts("History is empty");
        return 0;
    }

    while (i != hist_last) {
        const history_elt_t *entry = &hist_buf[i];
        char payload[256];
        const char *state = (entry->relay_status == RELAY_STATUS_CANCELED) ? "canceled" :
                            (entry->relay_status == RELAY_STATUS_PENDING) ? "pending" :
                            (entry->relay_status == RELAY_STATUS_RELAYED) ? "relayed" : "received";

        if (build_chat_payload(&entry->msg, entry->msg.has_ttl, payload, sizeof(payload)) != 0) {
            strncpy(payload, "<payload-error>", sizeof(payload) - 1);
            payload[sizeof(payload) - 1] = '\0';
        }

        printf("[slot=%d] crc=0x%08" PRIx32 " snr=%" PRId8
               " state=%s last_seen=%" PRIu32 " send_at=%" PRIu32
               " payload=\"%s\"\n",
               i,
               entry->crc,
               entry->first_snr,
               state,
               entry->last_seen,
               entry->time_to_send,
               payload);

        i = (i + 1) % HIST_SIZE;
    }

    return 0;
}

int parse_chat_msg(const char *buf, size_t len, chat_msg_t *out)
{
    if (buf == NULL || out == NULL) {
        return -1;
    }

    memset(out, 0, sizeof(chat_msg_t));

    // Sender
    strncpy(out->from, buf, NAME_LEN);
    out->from[NAME_LEN] = '\0';

    // Mode
    char mode = buf[NAME_LEN];
    if (mode != '@' && mode != '#') {
        return -1;
    }
    out->mode = mode;

    // Find two colons
    int colons[2] = {-1, -1};
    int ncolons = 0;

    for (size_t i = NAME_LEN + 1; i < len && ncolons < 2; i++) {
        if (buf[i] == ':') {
            colons[ncolons++] = (int)i;
        }
    }

    if (ncolons < 2) {
        return -1;
    }

    // Target
    int to_len = colons[0] - (NAME_LEN + 1);
    if (to_len <= 0 || to_len >= MAX_CHANNEL_LEN) {
        return -1;
    }
    strncpy(out->to, buf + NAME_LEN + 1, to_len);
    out->to[to_len] = '\0';

    // msg_id and optional ttl
    // Two cases:
    // 1) msg_id only: "123"
    // 2) msg_id and ttl: "123,456"
    char id_field[32] = {0};
    int  id_field_len = colons[1] - colons[0] - 1;
    if (id_field_len <= 0 || id_field_len >= (int)sizeof(id_field)) {
        return -1;
    }
    strncpy(id_field, buf + colons[0] + 1, id_field_len);

    char *comma = strchr(id_field, ',');
    if (comma != NULL) {
        // id_field = "123,456"
        // Set *comma to '\0' so id_field is now "123\0456"
        *comma = '\0';
        // So atoi find 123
        out->msg_id = atoi(id_field);
        // And atoi find 456
        out->ttl = atoi(comma + 1);
        out->has_ttl = 1;
    } else {
        // No ttl, id_field is just "123"
        out->msg_id = atoi(id_field);
        out->ttl = 0;
        out->has_ttl = 0;
    }

    // Content
    int content_start = colons[1] + 1;
    int content_len = (int)len - content_start;
    if (content_len < 0) content_len = 0;
    if (content_len >= (int)sizeof(out->content)) content_len = (int)sizeof(out->content) - 1;
    strncpy(out->content, buf + content_start, content_len);
    out->content[content_len] = '\0';

    return 0;
}

int snrth_cmd(int argc, char **argv)
{
    if (argc < 2) {
        printf("usage: snrth <get|set>\n");
        return -1;
    }

    if (strcmp(argv[1], "get") == 0) {
        printf("SNR threshold: %" PRId8 "\n", snr_threshold);
        return 0;
    }

    if (strcmp(argv[1], "set") == 0) {
        if (argc < 3) {
            printf("usage: snrth set <value>\n");
            return -1;
        }

        int tmp = atoi(argv[2]);
        if (tmp < -128 || tmp > 127) {
            printf("snrth: value out of int8_t range (-128..127)\n");
            return -1;
        }

        snr_threshold = (int8_t)tmp;
        printf("SNR threshold set to %" PRId8 "\n", snr_threshold);
        return 0;
    }

    printf("usage: snrth <get|set>\n");
    return -1;
}

static const shell_command_t shell_commands[] = {
	{ "init",    "Initialize SX1272",     					    init_sx1272_cmd },
	{ "setup",    "Initialize LoRa modulation settings",        lora_setup_cmd },
    { "implicit", "Enable implicit header",                     implicit_cmd },
    { "crc",      "Enable CRC",                                 crc_cmd },
    { "payload",  "Set payload length (implicit header)",       payload_cmd },
    { "random",   "Get random number from sx127x",              random_cmd },
    { "syncword", "Get/Set the syncword",                       syncword_cmd },
    { "rx_timeout", "Set the RX timeout",                       rx_timeout_cmd },
    { "channel",  "Get/Set channel frequency (in Hz)",          channel_cmd },
    { "register", "Get/Set value(s) of registers of sx127x",    register_cmd },
    { "send",     "Send raw payload string",                    send_cmd },
    { "listen",   "Start raw payload listener",                 listen_cmd },
    { "reset",    "Reset the sx127x device",                    reset_cmd },
    { "setname", "Set username (setname <username>)",           set_username_cmd },
    { "msg",      "Send msg (msg <@|#> <to> <txt> [ttl])",      msg_cmd },
    { "subscribe",   "Subscribe to a channel (#channel)",       subscribe_cmd },
    { "unsubscribe", "Unsubscribe from a channel (#channel)",   unsubscribe_cmd },
    { "users",   "List known users",                            users_cmd },
    { "hist",    "Display last recieved messages", print_hist },
    { "snrth",   "Get/Set SNR relay threshold",                 snrth_cmd },
    { NULL, NULL, NULL }
};

int main(void) {

    //init_sx1272_cmd(0,NULL);

    /* start the shell */
    puts("Initialization successful - starting the shell now");
    char line_buf[SHELL_DEFAULT_BUFSIZE];

    shell_run(shell_commands, line_buf, SHELL_DEFAULT_BUFSIZE);

    return 0;
}
