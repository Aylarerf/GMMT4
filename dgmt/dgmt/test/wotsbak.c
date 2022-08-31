#include <stdio.h>
#include <stdint.h>
#include <string.h>


#include "../wots.h"
#include "../randombytes.h"
#include "../params.h"
#include "../imt.h"
#include "../smt.h"
#include "../xmss_core.h"
#include "../dgmt.h"

int main()
{
    xmss_params params;
    // TODO test more different OIDs
    uint32_t oid = 0x00000001;

    /* For WOTS it doesn't matter if we use XMSS or XMSSMT. */
    xmss_parse_oid(&params, oid);
    /*
    printf("params=====\n");
    printf("func %u\n",params.func);
    printf("n %u\n",params.n);
    printf("padding_len %u\n",params.padding_len);
    printf("wots_w %u\n",params.wots_w);
    printf("wots_log_w %u\n",params.wots_log_w);
    printf("wots_len1 %u\n",params.wots_len1);
    printf("wots_len2 %u\n",params.wots_len2);
    printf("wots_len %u\n",params.wots_len1);
    printf("wots_sig_bytes %u\n",params.wots_sig_bytes);
    printf("full_height %u\n",params.full_height);
    printf("tree_height %u\n",params.tree_height);
    printf("d %u\n",params.d);
    printf("index_bytes %u\n",params.index_bytes);
    printf("sig_bytes %u\n",params.sig_bytes);
    printf("pk_bytes %u\n",params.pk_bytes);
    printf("sk_bytes %llu\n",params.sk_bytes);
    printf("bds_k %u\n",params.bds_k);
    
    unsigned char seed[params.n];
    unsigned char pub_seed[params.n];
    //unsigned char pk1[params.wots_sig_bytes];
    //unsigned char pk2[params.wots_sig_bytes];
    //unsigned char sig[params.wots_sig_bytes];
    //unsigned char m[params.n];
    uint32_t addr[8] = {0};

    randombytes(seed, params.n);
    randombytes(pub_seed, params.n);
    //randombytes(m, params.n);
    randombytes((unsigned char *)addr, 8 * sizeof(uint32_t));

    printf("Testing WOTS signature and PK derivation.. ");

    //wots_pkgen(&params, pk1, seed, pub_seed, addr);
    //wots_sign(&params, sig, m, seed, pub_seed, addr);
    //wots_pk_from_sig(&params, pk2, sig, m, pub_seed, addr);

    //if (memcmp(pk1, pk2, params.wots_sig_bytes)) {
    //    printf("failed!\n");
    //    return -1;
    // }
    //printf("successful.\n");


	//printf("WOTS Checking is done.\n");

	//define and initialize imt_seed;
	unsigned char imt_seed[params.n];
	randombytes(imt_seed, params.n);

	imt_node	*imt_head=NULL;
	imt_head = imt_setup(&params,imt_seed,pub_seed,addr);
	
	xmss_params smt_params;
	smt_high_params_initialization(&smt_params);
	printf("smt_params=====\n");
    printf("func %u\n",smt_params.func);
    printf("n %u\n",smt_params.n);
    printf("padding_len %u\n",smt_params.padding_len);
    printf("wots_w %u\n",smt_params.wots_w);
    printf("wots_log_w %u\n",smt_params.wots_log_w);
    printf("wots_len1 %u\n",smt_params.wots_len1);
    printf("wots_len2 %u\n",smt_params.wots_len2);
    printf("wots_len %u\n",smt_params.wots_len1);
    printf("wots_sig_bytes %u\n",smt_params.wots_sig_bytes);
    printf("full_height %u\n",smt_params.full_height);
    printf("tree_height %u\n",smt_params.tree_height);
    printf("d %u\n",smt_params.d);
    printf("index_bytes %u\n",smt_params.index_bytes);
    printf("sig_bytes %u\n",smt_params.sig_bytes);
    printf("pk_bytes %u\n",smt_params.pk_bytes);
    printf("sk_bytes %llu\n",smt_params.sk_bytes);
    printf("bds_k %u\n",smt_params.bds_k);

    
    unsigned char smt_seed[3 * params.n];
    randombytes(seed, 3 * params.n);
    
    printf("\n%p\n",(void *)imt_head);
    
    create_fallback_keys(&smt_params, imt_head, smt_seed);
    */
    
    //unsigned char in1[allot_node_size];
    //unsigned char in2[allot_node_size];
    /*allot in[4];
    for(uint32_t i=0; i < 4; i++){
        in[i].l=i;
        randombytes(in[i].value, allot_node_size);
    }
    
    printf("\nBefore==========");
    for(uint32_t j=0; j < 4; j++){
        printf("\nl = %u\n",in[j].l);
        for(uint32_t i=0; i < allot_node_size; i++)
            printf("%hhu ",in[j].value[i]);
    }

    sort_allot_node(in, 0, 3);    
 
    printf("\nAfter==========");   
    for(uint32_t j=0; j < 4; j++){
        printf("\nl = %u\n",in[j].l);
        for(uint32_t i=0; i < allot_node_size; i++)
            printf("%hhu ",in[j].value[i]);
    }
    */
    /*unsigned char   allocate_seed[params.n];
    randombytes(allocate_seed, params.n);
    uint32_t    lp[SMT_LEAF_NODES];
    
    create_allocation_list(&params,lp,(uint32_t)1, (uint32_t)2, (uint32_t)3, (uint32_t)3, allocate_seed);
    
    printf("\nL prime list==========\n");  
    for(uint32_t j=0; j < SMT_LEAF_NODES; j++)
        printf("%u ",lp[j]);
        
    printf("\n");
    
    for(uint32_t c=0;c<internal_imt_nodes;c++)
        smt_instance[c] = 0;
        
    request(1);*/
    
    dgmt_setup();
    request(const xmss_params *params, imt_node *head, const unsigned char *inseed, uint32_t   id)
    
    return 0;
}
