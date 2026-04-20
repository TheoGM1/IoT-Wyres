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

#include "net/netdev.h"
#include "net/netdev/lora.h"
#include "net/lora.h"

#include "board.h"

#include "sx127x_internal.h"
#include "sx127x_params.h"
#include "sx127x_netdev.h"

#include "fmt.h"

#define SX127X_LORA_MSG_QUEUE   (16U)
#ifndef SX127X_STACKSIZE
#define SX127X_STACKSIZE        (THREAD_STACKSIZE_DEFAULT)
#endif

#define MSG_TYPE_ISR            (0x3456)

static char stack[SX127X_STACKSIZE];
static kernel_pid_t _recv_pid;

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
static int SNRThreshold=32; // arbitrary value, maybe need to be changed

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

typedef struct history_elt{
    char from[NAME_LEN];
    int msg_id;
    char content[256];
    int8_t SNR;
}hist_elt_t;

static hist_elt_t hist_buf[32];
uint8_t hist_first=0;
uint8_t hist_last=0;

//////////////////////////////////////////

/// Functions declaration
static int find_oldest_user(void);
static void update_user(const char *name, int msg_id);
int in_hist(char* msg);

void update_hist(char* from,int from_l,int msg_id,char* msg,int msg_l,int8_t snr){
    int in=in_hist(msg);
    if(in!=0){
        in--;//decrement to get the real value
        hist_buf[in].SNR=snr;//update snr to not repeat the message too much
        return;
    }

    strncpy(hist_buf[hist_last].from,from,from_l);
    strncpy(hist_buf[hist_last].from,from,from_l);
    hist_buf[hist_last].msg_id=msg_id;
    strncpy(hist_buf[hist_last].content,msg,msg_l);
    hist_buf[hist_last].SNR=snr;
    hist_last=(hist_last+1)%32;
    if (hist_last==hist_first){
        hist_first=(hist_first+1)%32;
    }
}

int in_hist(char* msg){

    uint8_t i=hist_first;
    while(i!=hist_last){
        if (strcmp(msg,hist_buf[i].content)){
            return i+1;// return elt rank+1 to avoid collision with 0 for not found
        }
        i=(i+1)%32;
    }
    return 0;
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
            // printf(
            //     "{Payload: \"%s\" (%d bytes), RSSI: %i, SNR: %i, TOA: %" PRIu32 "}\n",
            //     message, (int)len,
            //     packet_info.rssi, (int)packet_info.snr,
            //     sx127x_get_time_on_air((const sx127x_t *)dev, len));
            char sender[NAME_LEN+1] = {0};
            char target[NAME_LEN+1] = {0};
            char msg_content[256] = {0};
            int msg_id = 0;

            strncpy(sender, message, NAME_LEN);
            sender[NAME_LEN] = '\0';

            strncpy(target, message + NAME_LEN + 1, NAME_LEN);
            target[NAME_LEN] = '\0';

            // Look for first ':'
            int first_colon = -1;
            int second_colon=-1;
            int cpt=0;
            for (size_t i = 0; i < len; i++) {
                if (message[i] == ':') {
                    if (cpt==0){
                        first_colon = i;
                        cpt++;
                    }else{
                        second_colon=i;
                        break;
                    }
                }
            }
            char buf[32]={0};
            strncpy(buf,message+first_colon+1,second_colon-first_colon-1);
            buf[second_colon-first_colon]='\0';
            msg_id=atoi(buf);
            strncpy(msg_content,message+second_colon,strlen(message)-second_colon);

            if (message[4]=='@'){
                if (strcmp(username,target)==0){
                    //the user is the target
                    printf("Private message received\n");
                    printf("@%s[%d] : %s\n",sender,msg_id,msg_content);
                    update_hist(sender,NAME_LEN,msg_id,msg_content,strlen(msg_content),packet_info.snr);
                    update_user(sender,msg_id);
                }else{
                    //not for us, #TODO redirection for LoRaWAN
                }
            }else if (message[4]=='#')
            {
                for (int i = 0; i < channel_count; i++) {
                        if (strcmp(subscribed_channels[i], target) == 0) {
                            printf("[CHANNEL #%s]@%s[%d] : %s\n",
                                target, sender, msg_id, msg_content);
                            update_hist(sender,NAME_LEN,msg_id,msg_content,strlen(msg_content),packet_info.snr);
                            update_user(sender, msg_id);
                            break;
                        }
                    }
            }else{
                printf("Unknown message format\n");
                printf(
                "{Payload: \"%s\" (%d bytes), RSSI: %i, SNR: %i, TOA: %" PRIu32 "}\n",
                message, (int)len,
                packet_info.rssi, (int)packet_info.snr,
                sx127x_get_time_on_air((const sx127x_t *)dev, len));
            }
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
    if (argc < 3) {
        printf("usage: %s <to|*> <message>\n", argv[0]);
        return 1;
    }

    if (username == NULL) {
        printf("Username should be set before sending messages. Please set it first.\n");
        return 1;
    }

    const char* type = argv[1];
    const char *target = argv[2];
    const char *message = argv[3];
    const int message_number = messageCounter++;

    /* '@' + ':' + ':' + '\0' = 4,  message_number (int32) max 10 digits */
    int payload_size = strlen(username) + strlen(target) + strlen(message) + 4 + 10;

    char *payload = malloc(payload_size);
    if (payload == NULL) {
        printf("Failed to allocate memory for payload\n");
        return 1;
    }

    snprintf(payload, payload_size, "%s%s%s:%d:%s", username, type, target, message_number, message);

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

int print_hist(int argc, char**argv){
    (void)argc;
    (void)argv;
    uint8_t i=hist_first;
    if (hist_first==hist_last){
        printf("History is empty");
        return 0;
    }
    while(i!=hist_last){
        printf("%s:%d:%s", 
                hist_buf[i].from,
                hist_buf[i].msg_id,
                hist_buf[i].content);
        i=(i+1)%32;
    }
    return 0;
}


int setSNRThreshold(int argc,char**argv){
    if (argc < 2) {
        printf("usage: %s <username>\n", argv[0]);
        return 1;
    }
    int newSNRThreshold= atoi(argv[1]);
    if (newSNRThreshold< 0){
        printf("Invalid input : '%s', abort\n",argv[1]);
    }else{
        SNRThreshold=newSNRThreshold;
    }
    return 0;
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
    { "msg",      "Send unicast/broadcast msg (msg <@|#> <to> <txt>)",msg_cmd },
    { "subscribe",   "Subscribe to a channel (#channel)",       subscribe_cmd },
    { "unsubscribe", "Unsubscribe from a channel (#channel)",   unsubscribe_cmd },
    { "users",   "List known users",                            users_cmd },
    { "hist",    "Display last recieved messages", print_hist },
    { "set_snr", "Set the SNR Threshold to the given value, default : 32",setSNRThreshold},
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

