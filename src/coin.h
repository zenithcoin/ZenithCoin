/*
 * coin.h
 *
 *  Created on: Apr 21, 2013
 *      Author: ceperez
 */

#ifndef COIN_H_
#define COIN_H_

#define COIN_NAME "ZenithCoin"

// https://en.bitcoin.it/wiki/Base58Check_encoding
#define COIN_ADDRESS_START  0

#define COIN_NOUNCE 90714
#define COIN_HASH_GEN_BLOCK "0x8e8484127b4043f1f534749aa860c8130fe609a79ab1390e6772b0a0d4471ff7"
#define COIN_MERKEL_ROOT  "0x8a358c1545426fdbc20e63498ecc1facad218377bb91a0b1c8965c059ac24c10"

#define COIN_SUBSIDY_HALFLIFE 840000
#define COIN_COINS_PER_BLOCK 12

#define COIN_DEFAULT_PORT 7733
#define COIN_TEST_DEFAULT_PORT 17733

#define COIN_RETARGET_TIME 3.5 * 24 * 60 * 60
#define COIN_RETARGET_SPACING 2.5 * 60
#define COIN_INITIAL_DIFF 20 // 1 / 2^10

#define COIN_DEV_ADDR_LENGTH 320
#define COIN_64 100000000
#define COIN_MAX_MONEY 84000000
#define COIN_SCRYPT_SCRATCHPAD_SIZE 256

#define COIN_DNS_SEED {"east.zenithcoin.com", "west.zenithcoin.com"},

#define COIN_IRC_CHANNELS 1
#define COIN_IRC_OFFSET 127

#define COIN_MESSAGE_START { 0xde, 0xfe, 0xc8, 0x73 }

#define COIN_SEED  

// 0x529a1347, 0x2d3de442,

#endif /* COIN_H_ */
