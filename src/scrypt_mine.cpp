/*-
 * Copyright 2009 Colin Percival, 2011 ArtForz, 2011 pooler, 2013 Balthazar
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 * 1. Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the distribution.
 *
 * THIS SOFTWARE IS PROVIDED BY THE AUTHOR AND CONTRIBUTORS ``AS IS'' AND
 * ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
 * ARE DISCLAIMED.  IN NO EVENT SHALL THE AUTHOR OR CONTRIBUTORS BE LIABLE
 * FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS
 * OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
 * HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT
 * LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY
 * OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF
 * SUCH DAMAGE.
 *
 * This file was originally written by Colin Percival as part of the Tarsnap
 * online backup system.
 */

#include <stdlib.h>
#include <stdint.h>
#include <xmmintrin.h>

extern "C" {
#include "scrypt-jane/scrypt-jane.h"
}

#include "scrypt_mine.h"


#include "util.h"
#include "net.h"


#if defined(__x86_64__)
#define SCRYPT_BUFFER_SIZE (3 * 131072 + 63)
#elif defined(__i386__)
#define SCRYPT_BUFFER_SIZE (131072 + 63)
#endif

void *scrypt_buffer_alloc() {
    return malloc(SCRYPT_BUFFER_SIZE);
}

void scrypt_buffer_free(void *scratchpad)
{
    free(scratchpad);
}



void scrypt_hash(const void* input, size_t inputlen, uint32_t *res, unsigned char Nfactor)
{
    return scrypt((const unsigned char*)input, inputlen,
                  (const unsigned char*)input, inputlen,
                  Nfactor, 0, 0, (unsigned char*)res, 32);
}



unsigned int scanhash_scrypt(block_header *pdata,
    uint32_t max_nonce, uint32_t &hash_count,
    void *result, block_header *res_header, unsigned char Nfactor)
{
    hash_count = 0;
    block_header data = *pdata;
    uint32_t hash[8];
    unsigned char *hashc = (unsigned char *) &hash;

    uint32_t n = 0;

    while (true) {

        data.nonce = n++;

        //scrypt(&data, 80, hash, scratchbuf);
        scrypt((const unsigned char*)&data, 80,
               (const unsigned char*)&data, 80,
               Nfactor, 0, 0, (unsigned char*)hash, 32);
        hash_count += 1;

        if (hashc[31] == 0 && hashc[30] == 0) {
            memcpy(result, hash, 32);

            return data.nonce;
        }

        if (n >= max_nonce) {
            hash_count = 0xffff + 1;
            break;
        }
    }

    return (unsigned int) -1;
}


unsigned int static scanHash_cryptoPP(char* pmidstate,
		char* pdata, char* phash1, char* phash,
		unsigned int& nHashesDone)
{
	const unsigned int pSHA256InitState[8] =
	{0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19};


    unsigned int& nNonce = *(unsigned int*)(pdata + 12);
    for (;;)
    {
        // Crypto++ SHA256
        // Hash pdata using pmidstate as the starting state into
        // pre-formatted buffer phash1, then hash phash1 into phash
        nNonce++;
        SHA256Transform(phash1, pdata, pmidstate);
        SHA256Transform(phash, phash1, pSHA256InitState);

        // Return the nonce if the hash has at least some zero bits,
        // caller will check if it has enough to reach the target
        if (((unsigned short*)phash)[14] == 0)
            return nNonce;

        // If nothing found after trying for a while, return -1
        if ((nNonce & 0xffff) == 0)
        {
            nHashesDone = 0xffff+1;
            return (unsigned int) -1;
        }
    }
}

