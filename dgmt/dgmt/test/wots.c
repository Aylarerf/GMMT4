#include <stdio.h>
#include <stdint.h>
#include <string.h>
#include <openssl/sha.h>
#include <openssl/aes.h>


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
        
    unsigned char seed[params.n];
    unsigned char pub_seed_imt[params.n];
    unsigned char pub_seed_smt[params.n];
    unsigned char manager_key[params.n];
    
    uint32_t addr[8] = {0};


    dgmt_setup();


    randombytes(seed, params.n);
    randombytes(pub_seed_imt, params.n);
    randombytes(pub_seed_smt, params.n);
    
    unsigned char imt_seed[params.n];
	randombytes(imt_seed, params.n);

	imt_node	*imt_head=NULL;
	imt_head = imt_setup(&params,imt_seed,pub_seed_imt,addr);
	unsigned char   imt_root[imt_node_len];
	memcpy(imt_root,imt_head[(1<<(imt_tree_height+1))-2].value,imt_node_len);
	
	xmss_params smt_params;
	smt_params_initialization(&smt_params);
	    
    unsigned char smtU_seed[3 * params.n];
    randombytes(smtU_seed, 3 * params.n);
    
    unsigned char smtL_seed[3 * params.n];
    randombytes(smtL_seed, 3 * params.n);
    
    //printf("\n%p\n",(void *)imt_head);
    
    create_fallback_keys(&smt_params, imt_head, smtU_seed);
    
    
    unsigned char   select_imt_node_seed[params.n];
    randombytes(select_imt_node_seed, params.n);
        
    unsigned char   allocate_seed[params.n];
    randombytes(allocate_seed, params.n);
    
    randombytes(manager_key, params.n);
    
    uint32_t    id=2;
    //printf("111111111111111111111\n\n");
	clock_t start_keydis,end_keydis;
	double cpu_time_used_keydis;
	start_keydis=clock();
    key_distribute(&smt_params, imt_head, smtU_seed, smtL_seed, select_imt_node_seed, allocate_seed, pub_seed_imt,manager_key, id);
   end_keydis=clock();
	cpu_time_used_keydis=((double)(end-start))/CLOCKS_PER_SEC;
	unsigned char		sm[2*(params.sig_bytes + params.pk_bytes) + XMSS_MLEN + 2*params.index_bytes + imt_tree_height*imt_node_len + params.n + AES_BLOCK_SIZE];
    unsigned char       m[XMSS_MLEN];
    randombytes(m, XMSS_MLEN);
	clock_t start_sign,end_sign;
	double cpu_time_used_sign;
	start_sign=clock();
    id = sign_dgmtU(&smt_params, sm, m, id);
	end_sign=clock();
	clock_t start_verify,end_verify;
	double cpu_time_used_verify;
	start_verify=clock();
    verify_dgmtU(&params, &smt_params, sm, imt_root);
	end_verify=clock();
	clock_t start_open,end_open;
	double cpu_time_used_open;
	start_open=clock();
    open_dgmt(&smt_params, sm, manager_key);
	end_open=clock();
	printf(" the runninb time is %lf \n",cpu_time_used_keydis);
	printf(" the runninb time is %lf \n",cpu_time_used_sign);
	printf(" the runninb time is %lf \n",cpu_time_used_verify);
	printf(" the runninb time is %lf \n",cpu_time_used_open);
    
    if (id)
        key_distribute(&smt_params, imt_head, smtU_seed, smtL_seed, select_imt_node_seed, allocate_seed, pub_seed_imt,manager_key, id-1);
        
    
    
    return 0;
}
