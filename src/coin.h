/*
 * coin.h
 *
 *  Created on: Apr 21, 2013
 *      Author: ceperez
 */

#ifndef COIN_H_
#define COIN_H_

#define COIN_NAME "VerityCoin"

#define COIN_ADDRESS_START  0

#define COIN_HASH_GEN_BLOCK "0xf0871eccf462f04457d127c5244350042782938fa036c66f658d67d5907572bc"


#define COIN_SUBSIDY_HALFLIFE 840000
#define COIN_COINS_PER_BLOCK 50

#define COIN_DEFAULT_PORT 9333
#define COIN_TEST_DEFAULT_PORT 19333

#define COIN_RETARGET_TIME 3.5 * 24 * 60 * 60
#define COIN_RETARGET_SPACING 30  // mintrate 2.5 * 60
#define COIN_INITIAL_DIFF 10 // 20

#define COIN_DEV_ADDR_LENGTH 10


#define COIN_MAX_MONEY 84000000

#define COIN_SCRYPT_SCRATCHPAD_SIZE 256

#define COIN_MERKEL_ROOT  "0xae380b4d8efa60d2db4905d91a2b4bd977c0f8ebe6b6ba3d1e162372bb6e9aa6"

#define COIN_DNS_SEED {"node.freico.in", "seed.freico.in"},{"abacus.freico.in", "fledge.freico.in"},

#define COIN_SEED  

// 0x529a1347, 0x2d3de442,

#endif /* COIN_H_ */
