/*Created by Sabyasachi Karati*/

#include <stdint.h>
#include <string.h>
#include <stdlib.h>
#include <stdio.h>
#include <openssl/sha.h>
#include <openssl/aes.h>
#include <stddef.h>
#include <unistd.h>
#include <fcntl.h>
#include <sys/types.h>
#include <sys/stat.h>


#include "dgmt.h"
#include "params.h"
#include "imt.h"
#include "smt.h"
#include "wots.h"
#include "xmss_core.h"
#include "xmss_commons.h"
#include "hash.h"
#include "hash_address.h"
#include "utils.h"
#include "params.h"
#include "fips202.h"



void create_user_filename(char filename[], uint32_t id){
    uint32_t    i,l;
    
    l=DIGITS_USER-1;
    for(i=DIGITS_USER; i>0; i--){
        filename[l] = (uint8_t )((id%10) + '0');
        id = id/10;
        l--;
    }
    filename[DIGITS_USER] = 0; 
}


void create_smt_filename(char filename[], uint32_t i0, 
                     uint32_t i1, uint32_t j, uint32_t k){
    uint32_t    i,l;
    
    l=DIGITS_IMT_HEIGHT-1;
    for(i=DIGITS_IMT_HEIGHT; i>0; i--){
        filename[l] = (uint8_t )((i0%10) + '0');
        i0 = i0/10;
        l--;
    }
    
    l=DIGITS_IMT_HEIGHT+DIGITS_IMT_LAYER-1;
    for(i=DIGITS_IMT_LAYER; i>0; i--){
        filename[l] = (uint8_t )((i1%10) + '0');
        i1 = i1/10;
        l--;
    }

    l=DIGITS_IMT_HEIGHT+DIGITS_IMT_LAYER+DIGITS_SMT_PER_IMT-1;
    for(i=DIGITS_SMT_PER_IMT; i>0; i--){
        filename[l] = (uint8_t )((j%10) + '0');
        j = j/10;
        l--;
    }

    l=FILENAME_LEN-1;
    for(i=DIGITS_SMT_LEAF; i>0; i--){
        filename[l] = (uint8_t )((k%10) + '0');
        k = k/10;
        l--;
    } 
    
    filename[FILENAME_LEN] = 0;
}

void create_m_user(uint32_t id){
    int     fd;
    char    filename[FILENAME_LEN+1]={0};
    char    pathname[50+FILENAME_LEN+1]={0};
    
    uint32_t    i0,i1,j,l;
    uint32_t    init_smt = 0;
    uint32_t    len=sizeof(uint32_t);
    
    create_user_filename(filename, id);
    printf("id = %u, filename = %s\n",id,filename);
    
    sprintf(pathname,"%s%s",DIR_M_USER,filename);
    printf("id = %u, pathname = %s\n\n",id,pathname);    
        
    if((fd = open(pathname, O_WRONLY | O_CREAT | O_TRUNC, MANAGER_PERMISSION))==-1){
            printf("File: %s creation error\n",pathname);
            exit(0);
        }else{
            printf("File: %s creation success\n",pathname);
            
            for(i0=1;i0<=imt_tree_height;i0++){   // for each height except root
                l = 1 << i0;
                for(i1=0;i1<l;i1++){            // for each node at height i0
                    /*for each node (i0,i1) initialize j=0,k=0*/
                    if(write(fd,&init_smt,len)!=len){
                        printf("m_user initialization error 01: %u,%u,%u\n",i0,i1,j);
                        exit(0);
                    }
                    if(write(fd,&init_smt,len)!=len){
                        printf("m_user initialization error 02: %u,%u,%u\n",i0,i1,j);
                        exit(0);
                    }//else
                }
            }
            close(fd);
        }
        
        printf("m_user creation success for id = %u\n\n\n\n",id);
}


void dgmt_setup(){
    struct stat st = {0};

    /*Create required directory*/

    if (stat("./dgmmt", &st) == -1) {
        mkdir("./dgmmt", 0700);
    }
    
    if (stat("./dgmmt/manager", &st) == -1) {
        mkdir("./dgmmt/manager", 0700);
    }
    
    if (stat("./dgmmt/manager/m_user", &st) == -1) {
        mkdir("./dgmmt/manager/m_user", 0700);
    }
    
    if (stat("./dgmmt/manager/smt", &st) == -1) {
        mkdir("./dgmmt/manager/smt", 0700);
    }
    
    if (stat("./dgmmt/manager/smt/smtU", &st) == -1) {
        mkdir("./dgmmt/manager/smt/smtU", 0700);
    }

    if (stat("./dgmmt/manager/smt/smtD", &st) == -1) {
        mkdir("./dgmmt/manager/smt/smtD", 0700);
    }

    if (stat("./dgmmt/user", &st) == -1) {
        mkdir("./dgmmt/user", 0700);
    }
    
    if (stat("./dgmmt/fallback", &st) == -1) {
        mkdir("./dgmmt/fallback", 0700);
    }


    for(uint32_t id=0;id<MAX_GROUP_MEMBER;id++)
        create_m_user(id);

    for(uint32_t c=0;c<MAX_GROUP_MEMBER;c++)
        request_number[c] = 0;
}


void create_allocation_list(const xmss_params *params, uint32_t lp[],
                            uint32_t i0, uint32_t i1, uint32_t j,
                            uint32_t k, const unsigned char   *inseed){
    unsigned char   buf[32];
    uint32_t        addr[8] = {0};
    allot           l_list[SMT_LEAF_NODES];
    uint32_t        i;
    
    
    set_hash_addr(addr, 0);
    set_key_and_mask(addr, 0);    
    addr[4] = i0;
    addr[3] = i1;
    addr[2] = j;
    addr[1] = k;
    
    for(i=0; i < SMT_LEAF_NODES; i++){
        addr[0] = i;
        addr_to_bytes(buf, addr);
        l_list[i].l = i;
        prf(params, l_list[i].value, buf, inseed);
    }
    
    sort_allot_node(l_list, 0, SMT_LEAF_NODES-1, SMT_N);

    
    for(i=0; i < SMT_LEAF_NODES; i++)
        lp[l_list[i].l] = i;
}


void create_smtu_keypair(const xmss_params *params, const unsigned char *inseedU, uint32_t i0, uint32_t i1, uint32_t j){
    int                 fd;
    unsigned char       pk[params->pk_bytes];
    unsigned char       sk[params->sk_bytes];
    unsigned char       smt_seed[3 * params->n];
    uint32_t            k=0;
    char                filename[FILENAME_LEN+1]={0};
    char                pathname[50+FILENAME_LEN+1]={0};
    uint32_t            smt_addr[4] = {0};
    unsigned char       buf[32];
    uint32_t            addr[8] = {0};
    
    /*create pathname of SMU_U key to the leaf node of (i0,i1,j,0)*/
    printf("\n\n\nCreate SMT U\n");
    create_smt_filename(filename,i0,i1,j,k);
    printf("SMT_U filename = %s\n",filename);

    sprintf(pathname,"%s%s",DIR_SMTU,filename);
    printf("SMT_U  pathname = %s\n\n",pathname);
    
    if((fd = open(pathname, O_WRONLY | O_CREAT | O_TRUNC, MANAGER_PERMISSION))==-1){
    	printf("File: %s creation error from create_smtu\n",pathname);
    	exit(0);
    }else{
    	set_hash_addr(smt_addr, 0);
		set_key_and_mask(smt_addr, 0);
		
        smt_addr[0] = 0;
        smt_addr[1] = j;
        smt_addr[2] = i1;
        smt_addr[3] = i0;
        set_smt_tree_addr(addr, smt_addr);
        
        set_chain_addr(addr, 1);
        addr_to_bytes(buf, addr);
        prf(params, smt_seed, buf, inseedU);

        set_chain_addr(addr, 2);
        addr_to_bytes(buf, addr);
        prf(params, smt_seed+params->n, buf, inseedU);

        set_chain_addr(addr, 3);
        addr_to_bytes(buf, addr);
        prf(params, smt_seed+2 * params->n, buf, inseedU);
               
        xmssmt_core_seed_keypair(params, pk, sk, smt_seed);
        
        if((unsigned long long)write(fd, sk,params->sk_bytes)!=params->sk_bytes){
            printf("File: %s creat smt_sk error 1\n",pathname);
            exit(0);
        }

        close(fd);
    }
}

void create_smtu_nextkey(const xmss_params *params, uint32_t i0, uint32_t i1, uint32_t j, uint32_t k){
    int                 fd;
    unsigned char       sk[params->sk_bytes];
    char                filename[FILENAME_LEN+1]={0};
    char                pathname[50+FILENAME_LEN+1]={0};
    
    
    /*create pathname of SMU_U key to the leaf node of (i0,i1,j,0)*/
    printf("\n\n\nCreate SMT U\n");
    create_smt_filename(filename,i0,i1,j,k-1);
    printf("SMT_U filename = %s\n",filename);

    sprintf(pathname,"%s%s",DIR_SMTU,filename);
    printf("SMT_U  pathname = %s\n\n",pathname);
    
    if((fd = open(pathname, O_RDONLY, MANAGER_PERMISSION))==-1){
    	printf("File: %s open error from create_smtu_nextkey\n",pathname);
        exit(0);
    }else{
       	if((unsigned long long)read(fd, sk, params->sk_bytes)!=params->sk_bytes){
			printf("File: %s retrieving secret key error 1\n",pathname);
			exit(0);
		}else{
			close(fd);
			xmssmt_core_next_key(params, sk);
			
		    printf("\n\n\nCreate SMT U\n");
		    create_smt_filename(filename,i0,i1,j,k);
		    printf("SMT_U filename = %s\n",filename);
	
		    sprintf(pathname,"%s%s",DIR_SMTU,filename);
		    printf("SMT_U  pathname = %s\n\n",pathname);

			if((fd = open(pathname, O_WRONLY | O_CREAT | O_TRUNC, MANAGER_PERMISSION))==-1){
    			printf("File: %s creation error from create_smtu\n",pathname);
    			exit(0);
    		}else{
    			if((unsigned long long)write(fd, sk,params->sk_bytes)!=params->sk_bytes){
            		printf("File: %s creat smt_sk error 1\n",pathname);
            		exit(0);
        		}
    		}
		}

    	
    	
    	
        close(fd);
    }
}

void create_smtd(const xmss_params *params, const unsigned char *inseedL, const unsigned char *alloc_seed, 
                const unsigned char *manager_key, uint32_t i0, uint32_t i1, uint32_t j, uint32_t k){
                     
    int                 fd;
    unsigned char       smt_seed[3 * params->n];
    char                filename[FILENAME_LEN+1]={0};
    char                pathname[50+FILENAME_LEN+1]={0};
    uint32_t            smt_addr[4] = {0};
    unsigned char       buf[32];
    uint32_t            addr[8] = {0};
    uint32_t            lp[SMT_LEAF_NODES];
    uint32_t            lpi[SMT_LEAF_NODES];
    uint32_t            count = 0;
    uint32_t            len;
    
    unsigned char       smtd_pk[params->pk_bytes];
    unsigned char       smtd_sk[params->sk_bytes];
    unsigned char       sm[params->sig_bytes + XMSS_MLEN +AES_BLOCK_SIZE];
    unsigned char       enc_label[AES_BLOCK_SIZE*SMT_LEAF_NODES];
    unsigned char       label[AES_BLOCK_SIZE];
    unsigned long long  smlen;
    uint32_t            i0i1;

    AES_KEY             enc_key;

    /*create pathname of SMU_U key to the leaf node of (i0,i1,j,0)*/
    printf("\n\n\nCreate SMT D\n");
    create_smt_filename(filename,i0,i1,j,k);
    printf("SMT_D filename = %s\n",filename);

    sprintf(pathname,"%s%s",DIR_SMTD,filename);
    printf("SMT_D  pathname = %s\n\n",pathname);
    
    if((fd = open(pathname, O_WRONLY | O_CREAT | O_TRUNC, MANAGER_PERMISSION))==-1){
      	printf("File: %s creation error from create_smtd\n",pathname);
     	exit(0);
    }else{
        /*write the number of keys assigned to each user*/
        len=sizeof(uint32_t);
        for(int i= 0; i< MAX_GROUP_MEMBER; i++){
            if(write(fd, &count,len)!=len){ //correct version
            //if(write(fd, &i,len)!=len){     //test version
                printf("File: %s initial count writing error 1\n",pathname);
                exit(0);
            }
        }
        
        
        /*Create the randomized list of assignment of keys*/
        create_allocation_list(params,lp,i0,i1,j,k,alloc_seed);
        //printf("\n");
        //printf("\n\n\nI am here111111111111111\n\n\n");
        //for(int i=0; i<SMT_LEAF_NODES;i++)
        //    printf("%u ",lp[i]);
        //printf("\n");
        //printf("\n\n\nI am here222222222222222\n\n\n");
        len = len * SMT_LEAF_NODES;
        if(write(fd, lp, len)!=len){
                printf("File: %s initial count writing error 1\n",pathname);
                exit(0);
        }
                
        for(int i=0; i<SMT_LEAF_NODES; i++)
            lpi[lp[i]] = i;
        
        
        memset(enc_label,0,AES_BLOCK_SIZE*SMT_LEAF_NODES);
        AES_set_encrypt_key(manager_key, 256, &enc_key);
        //AES_set_decrypt_key(manager_key, 256, &dec_key);
        
        //create labels
        for(int i=0; i<SMT_LEAF_NODES; i++){
            i0i1 = i1;
            i0i1 = i1 | (i0<<24);
 			ull_to_bytes(label, 4, i0i1);
 			ull_to_bytes(label+4, 4, j);
 			ull_to_bytes(label+8, 4, k);
 			ull_to_bytes(label+12, 4, lpi[i]);
 			
 			AES_encrypt(label, enc_label + AES_BLOCK_SIZE*i, &enc_key);
 			
	    }
         
        smt_addr[0] = k;
        smt_addr[1] = j;
        smt_addr[2] = i1;
        smt_addr[3] = i0;
        set_smt_tree_addr(addr, smt_addr);
        
        set_chain_addr(addr, 1);
        addr_to_bytes(buf, addr);
        prf(params, smt_seed, buf, inseedL);

        set_chain_addr(addr, 2);
        addr_to_bytes(buf, addr);
        prf(params, smt_seed+params->n, buf, inseedL);

        set_chain_addr(addr, 3);
        addr_to_bytes(buf, addr);
        prf(params, smt_seed+2 * params->n, buf, inseedL);
        
        //randombytes(inseedL, 3 * params->n);     
        xmssmt_core_seed_keypair_dgmt_D(params, smtd_pk, smtd_sk, smt_seed, enc_label);
    
        //write the pk to the file
    	if(write(fd, smtd_pk, params->pk_bytes)!=params->pk_bytes){
        	printf("File: %s write pk error 1\n",pathname);
            exit(0);
        }
        
        for(int i = 0; i<SMT_LEAF_NODES; i++){
            memset(sm,0,params->sig_bytes + XMSS_MLEN+AES_BLOCK_SIZE);
            xmssmt_core_sign_dgmtM(params, smtd_sk, sm, &smlen, XMSS_MLEN, enc_label);
            memcpy(sm+params->sig_bytes + XMSS_MLEN, enc_label+i*AES_BLOCK_SIZE,AES_BLOCK_SIZE);
            //memcpy(sm+params->sig_bytes + XMSS_MLEN+AES_BLOCK_SIZE, smtd_pk,params->pk_bytes);
            //printf("create_smtD: Seq No: %d, Verification %d\n",i,xmssmt_core_sign_open_dgmt(params,mout,&mlen,sm,smlen,smtd_pk));
            
            if(write(fd, sm, (params->sig_bytes + XMSS_MLEN + AES_BLOCK_SIZE))!=(params->sig_bytes + XMSS_MLEN + AES_BLOCK_SIZE)){
                printf("File: %s write sk error 1\n",pathname);
                exit(0);
            }
        }
        
        close(fd);
    }
    
}


void sign_dgmtM(const xmss_params *imt_params, const xmss_params *params, imt_node *head, 
                     unsigned char *pub_seed_imt, uint32_t   id, uint64_t i0, uint64_t i1,
                     uint64_t j, uint64_t k, unsigned char *sm){

    int                 fd_smtu,fd_smtd,fd_muser;                     //file descriptors
    char                filename[FILENAME_LEN+1]={0};
    char                pathname[50+FILENAME_LEN+1]={0};
    unsigned long long  skip;
    long long int		len;
    
    unsigned char       smtu_sk[params->sk_bytes];
    unsigned char       smtd_pk[params->pk_bytes];
    unsigned char       m[XMSS_MLEN];
    unsigned char       smd[params->sig_bytes + XMSS_MLEN + params->pk_bytes + AES_BLOCK_SIZE];
    unsigned char		smu[params->sig_bytes + XMSS_MLEN + params->pk_bytes];
    unsigned long long  smlen;

    
    uint32_t            count_id,key_number;
    unsigned long long  seek;
            
    /*retrieve the SMU_U keys from the file corresponding to the leaf node of (i0,i1,j,k)*/
    create_smt_filename(filename,i0,i1,j,k);
    printf("SMT_U filename = %s\n",filename);

    sprintf(pathname,"%s%s",DIR_SMTU,filename);
    printf("SMT_U  pathname = %s\n\n",pathname);
    
           
    if((fd_smtu = open(pathname, O_RDONLY, MANAGER_PERMISSION))==-1){	//open the smtu file for i0,i1,j,k
      	printf("File: %s open read error for request 5\n",pathname);
       	exit(0);
    }else{
        //upon successful opeing of smtu file, open the newly created smtd file for i0,i1,j,k
        sprintf(pathname,"%s%s",DIR_SMTD,filename);
        printf("SMT_D  pathname = %s\n\n",pathname);
        if((fd_smtd = open(pathname, O_RDWR, MANAGER_PERMISSION))==-1){
        	printf("File: %s open read error for request 3\n",pathname);
        	exit(0);
        }else{
        	//retrieve how many keys has been distributed to user id that is key count
		   	len = sizeof(uint32_t);
		   	seek = id*len;
		   	lseek(fd_smtd, seek, SEEK_SET);
		   	if(read(fd_smtd, &count_id, len)!=len){
		  	   	printf("File: %s read count_id error 2\n",pathname);
		       	exit(0);
		   	}
		        
			//retrieve the sequence number of the key to assign to user id  
			seek = (MAX_GROUP_MEMBER + KEYS_PER_USER_PER_TREE*id + count_id)*len;
			lseek(fd_smtd, seek, SEEK_SET);
		   	if(read(fd_smtd, &key_number, len)!=len){
		   	   	printf("File: %s read count_id error 2\n",pathname);
		       	exit(0);
		   	}
		        
		    //retrieve the key  
    		seek = len * (MAX_GROUP_MEMBER+SMT_LEAF_NODES);// + keynumber * params->sk_bytes;
    		lseek(fd_smtd, seek, SEEK_SET);
    		
    		//retrieve pk
    		if(read(fd_smtd, smtd_pk, params->pk_bytes)!=params->pk_bytes){
				printf("File: %s retrieving secret key error 1\n",pathname);
			    exit(0);
			}
    	
    		//read sm from for i0,i1,j,k
    		len = (params->sig_bytes + XMSS_MLEN + AES_BLOCK_SIZE);
        	seek = key_number * len;
    		lseek(fd_smtd, seek, SEEK_CUR);

			if(read(fd_smtd, smd, len)!=len){
				printf("File: %s retrieving secret key error 1\n",pathname);
			    exit(0);
			}
			
			// Update count id in the SMTD file for i0,i1,j,k
			len = sizeof(uint32_t);
	       	seek = id*len;
	       	lseek(fd_smtd, seek, SEEK_SET);
	       	count_id++;
	       	if(write(fd_smtd, &count_id, len)!=len){
	    	   	printf("File: %s update count_id error 2\n",pathname);
	           	exit(0);
	       	}
	       	
	       	close(fd_smtd);
    			
       	}
           	
       	if((unsigned long long)read(fd_smtu, smtu_sk, params->sk_bytes)!=params->sk_bytes){
			printf("File: %s retrieving secret key error 1\n",pathname);
			exit(0);
		}else{
			memcpy(smu + params->sig_bytes + XMSS_MLEN, smtu_sk + params->index_bytes + 2*params->n, params->pk_bytes);
			xmssmt_core_sign(params, smtu_sk, smu, &smlen, smtd_pk,params->n);
		}
            
        close(fd_smtu);
            
        // Construct the signature sm combining smu and smd
        memset(sm,0,2*(params->sig_bytes + params->pk_bytes) + XMSS_MLEN + 2*params->index_bytes+imt_tree_height*imt_node_len+ AES_BLOCK_SIZE);
        memcpy(sm,smd,params->sig_bytes + XMSS_MLEN);
        memcpy(sm+params->sig_bytes + XMSS_MLEN, smtd_pk, params->pk_bytes);
        
        memcpy(sm+params->sig_bytes + XMSS_MLEN + params->pk_bytes,smu,params->sig_bytes);
        memcpy(sm+2*params->sig_bytes + XMSS_MLEN + params->pk_bytes,smu+params->sig_bytes + XMSS_MLEN,params->pk_bytes);
        ull_to_bytes(sm + 2*(params->sig_bytes + params->pk_bytes) + XMSS_MLEN, params->index_bytes, (unsigned long long)i0);
      	ull_to_bytes(sm + 2*(params->sig_bytes + params->pk_bytes) + XMSS_MLEN + params->index_bytes, params->index_bytes, (unsigned long long)i1);
        	
       	len = 2*(params->sig_bytes + params->pk_bytes) + XMSS_MLEN + 2*params->index_bytes;
       	for(int i=i0;i>0;i--){
       		seek = (internal_imt_nodes - (1 << (i+1)) + 2); //index of the first node from left at height i0 in head
       		if(i1 & 0x1){
       			memcpy(sm+len,head[seek+i1-1].value,imt_node_len);
       		}else{
       			memcpy(sm+len,head[seek+i1+1].value,imt_node_len);
       		}
       		len = len + imt_node_len;
       		i1 = i1>>1;	
       	}
       	len = 2*(params->sig_bytes + params->pk_bytes) + XMSS_MLEN + 2*params->index_bytes+imt_tree_height*imt_node_len;
       	memcpy(sm+len,pub_seed_imt,params->n);
       	memcpy(sm+len+params->n,smd+params->sig_bytes + XMSS_MLEN,AES_BLOCK_SIZE);
        	
        randombytes(m, XMSS_MLEN);
       	sign_dgmtU(params, sm, m);
       	//mlen = XMSS_MLEN;
       	verify_dgmtU(imt_params, params, sm, head);
 	}
	
	
    //check whether there is any key to assign to user id
    if(count_id >= KEYS_PER_USER_PER_TREE-1){              // true if there is no key left
	    //check whether there is any leaf unused in the SMT_U for (i0,i1,j)
		if(k >= (SMT_LEAF_NODES-1)){                    // true if there is no more leaf in the SMT_U for (i0,i1,j)
        	//check whether there is any SMT_U tree unused in the IMT for (i0,i1)
        	if(j >= (SMT_PER_IMT_NODE-1)){              // true if there is no more SMT_U tree in the IMT for (i0,i1)
        	    printf("\nNo more key for user %u from IMT node (%lu,%lu)\n",id,i0,i1);
                return;
            }else{
        		//update as j<-j+1 and k<-0
                j = j+1;
                k = 0;
            }    
		}else{
	        //update as k<-k+1
            k = k+1;
        }
                
        //reflect the updated values of j and k in /dgmmt/manager/m_user/id file
		create_user_filename(filename, id);
        printf("id = %u, filename = %s\n",id,filename);
                
        sprintf(pathname,"%s%s",DIR_M_USER,filename);
        printf("id = %u, pathname = %s\n\n",id,pathname);    

        if((fd_muser = open(pathname, O_WRONLY, MANAGER_PERMISSION))==-1){
	        printf("File: %s open write error from request 4\n",pathname);
            exit(0);
        }else{
            len = sizeof(uint32_t);
            skip = (((1<<i0)-2)+i1)*2*len;
            lseek(fd_muser, skip, SEEK_SET);
            if(write(fd_muser, &j,len)!=len){
	            printf("File: %s modify j error from request 4\n",pathname);
               	exit(0);
            }
            if(write(fd_muser, &k,len)!=len){
 	           	printf("File: %s modify k error from request 4\n",pathname);
                exit(0);
            }
            close(fd_muser);
		}
	}
}



/*User id askes for new B keys*/

void key_distribute(const xmss_params *imt_params, const xmss_params *params, imt_node *head, const unsigned char *inseedU, 
            const unsigned char *inseedL, const unsigned char   *select_imt_node_seed, const unsigned char   *alloc_seed,
            unsigned char *pub_seed_imt, unsigned char *manager_key, uint32_t id){
    
    int                 fd_smtu,fd_muser, fd_user;                    //file descriptors
    uint32_t            i0,i1,j=-1,k=-1;                              //indexing of leaf nodes
    char                filename[FILENAME_LEN+1]={0};
    char                pathname[50+FILENAME_LEN+1]={0};
    unsigned char       i0i1_c[32], buf[32];
    unsigned long long  i0i1_i;
    unsigned long long  skip;
    uint32_t            addr[8] = {0};
    long long int		len;
    unsigned char		sm[2*(params->sig_bytes + params->pk_bytes) + XMSS_MLEN + 2*params->index_bytes+imt_tree_height*imt_node_len+params->n+AES_BLOCK_SIZE];
    
    
    /*randomly seclect (i0,i1)*/
    
    request_number[id]++;                                       //update the value of previously made 
                                                                //requests by user id by 1
    if(request_number[id]<=MAX_REQUEST){
    	create_user_filename(filename, id);
		printf("id = %u, filename = %s\n",id,filename);
		
		sprintf(pathname,"%s%s",DIR_USER,filename);
		printf("id = %u, pathname = %s\n\n",id,pathname);
		
		if((fd_user = open(pathname, O_WRONLY | O_CREAT | O_TRUNC, MANAGER_PERMISSION))==-1){
			printf("\nUser file: %s creation error\n",pathname);
			exit(0);
		}else{
			len = 0;
			if(write(fd_user, &len,sizeof(uint32_t))!=sizeof(uint32_t)){
						printf("File: %s B_KEYS_PER_USER writing error\n",pathname);
						exit(0);
			}
    		for(int count=0; count < B_KEYS_PER_USER; count++){
				set_hash_addr(addr, 0);
				set_key_and_mask(addr, 0);
				addr[0] = request_number[id];                               //present request number by user id
				addr[1] = id;                                               //set the user id number
				addr_to_bytes(buf, addr);
				prf(params, i0i1_c, buf, select_imt_node_seed);             //get the pseudo random number for i0 and i1
				i0i1_i = bytes_to_ull(i0i1_c, 32);                          //convert char string to ull
				
				i0 = (uint32_t)(((i0i1_i & 0xFF)%imt_tree_height)+1);       //take first byte as height
				i1 = (uint32_t)((i0i1_i >> 8)%(1<<i0));                     //take the remaining as node at the height i0
				
				/*retrieve (j,k), j = SMT instance and k = leaf node of the upper SMT tree*/
				create_user_filename(filename, id);
				printf("id = %u, filename = %s\n",id,filename);
		
				sprintf(pathname,"%s%s",DIR_M_USER,filename);
				printf("id = %u, pathname = %s\n\n",id,pathname);    
				
				if((fd_muser = open(pathname, O_RDONLY, MANAGER_PERMISSION))==-1){
					printf("File: %s open error from request 1\n",pathname);
					exit(0);
				}else{
					len = sizeof(uint32_t);
					skip = (((1<<i0)-2)+i1)*2*len;
					lseek(fd_muser, skip, SEEK_SET);
					if(read(fd_muser, &j,len)!=len){
						printf("File: %s retrieve j error from request 1\n",pathname);
						exit(0);
					}
					if(read(fd_muser, &k,len)!=len){
						printf("File: %s retrieve k error from request 1\n",pathname);
						exit(0);
					}
					close(fd_muser);
				}

				printf("\n\nid = %u, request number = %lu, imt node = (%u,%u), j = %u, k = %u\n",id,request_number[id],i0,i1,j,k);
				
				
				/*retrieve the SMU_U keys from the file corresponding to the leaf node of (i0,i1,j,k)*/
				create_smt_filename(filename,i0,i1,j,k);
				printf("SMT_U filename = %s\n",filename);

				sprintf(pathname,"%s%s",DIR_SMTU,filename);
				printf("SMT_U  pathname = %s\n\n",pathname);
				
				if((fd_smtu = open(pathname, O_RDONLY, MANAGER_PERMISSION))==-1){
					printf("File: %s does not exist for request 2\n",pathname);
					if(k==0){   //k=0 means that the creation of the first instance of smtU_{i0,i1,j,0}
						create_smtu_keypair(params, inseedU,i0,i1,j);        //if the file does not exist, create one
					}else{
						create_smtu_nextkey(params,i0,i1,j,k);
					}
					create_smtd(params, inseedL, alloc_seed, manager_key, i0, i1, j, k);
					
					sign_dgmtM(imt_params, params, head, pub_seed_imt, id, i0, i1, j, k, sm);
				}else{
					sign_dgmtM(imt_params, params, head, pub_seed_imt, id, i0, i1, j, k, sm);
					close(fd_smtu);
				}
				len = 2*(params->sig_bytes + params->pk_bytes) + XMSS_MLEN + 2*params->index_bytes+imt_tree_height*imt_node_len+params->n+AES_BLOCK_SIZE;
				if(write(fd_user,sm,len)!=len){
						printf("File: %s user key writing error\n",pathname);
						exit(0);
				}
			}
			close(fd_user);
		}
    }else
    	printf("\nNo more Keys for user %u\n",id);
}


void sign_dgmtU(const xmss_params *params, unsigned char *sm, unsigned char *m){
    char                filename[FILENAME_LEN+1]={0};
    char                pathname[50+FILENAME_LEN+1]={0};


	const unsigned char *pub_root = sm +params->sig_bytes + XMSS_MLEN;
	const unsigned char *pub_seed = sm +params->sig_bytes + XMSS_MLEN + params->n;
	unsigned char 		mout[params->sig_bytes + XMSS_MLEN];
					
	unsigned char root[params->n];
	unsigned char *mhash = root;
	unsigned long long idx;
	uint32_t idx_leaf;

/*    	create_user_filename(filename, id);
		printf("id = %u, filename = %s\n",id,filename);
		
		sprintf(pathname,"%s%s",DIR_USER,filename);
		printf("id = %u, pathname = %s\n\n",id,pathname);

*/
	uint32_t ots_addr[8] = {0};
	
	
	set_type(ots_addr, XMSS_ADDR_TYPE_OTS);
			    
    // Put the message in the right place
    memcpy(sm + params->sig_bytes, m, XMSS_MLEN);
    memcpy(mout + params->sig_bytes, m, XMSS_MLEN);
				    
    // Read and use the current index from the present signature.
    idx = (unsigned long)bytes_to_ull(sm, params->index_bytes);
    				
    hash_message(params, mhash, sm + params->index_bytes, pub_root, idx,
   				mout + params->sig_bytes - params->padding_len - 3*params->n,
   				XMSS_MLEN);
				    
    set_type(ots_addr, XMSS_ADDR_TYPE_OTS);
				    
    idx_leaf = (idx & ((1 << params->tree_height)-1));
	idx = idx >> params->tree_height;

	set_layer_addr(ots_addr, 0);
	set_tree_addr(ots_addr, idx);
	set_ots_addr(ots_addr, idx_leaf);

					
	// Compute a WOTS signature. 
	wots_sign_dgmtM(params, sm + params->index_bytes + params->n, root, pub_seed, ots_addr);
					
}

void verify_dgmtU(const xmss_params *imt_params, const xmss_params *params, unsigned char *sm, imt_node *head){
	int					fd_fk;
    unsigned char       smtu_pk[params->pk_bytes];
    unsigned char       smtd_pk[params->pk_bytes];
    unsigned char       mout[params->sig_bytes + XMSS_MLEN];
    unsigned char       smd[params->sig_bytes + XMSS_MLEN + AES_BLOCK_SIZE];
    unsigned char		smu[params->sig_bytes + XMSS_MLEN];
    unsigned char		imt_i0i1[imt_node_len];
    unsigned char		fallbackkey[2*AES_BLOCK_SIZE];
    unsigned long long	i0,i1,j;
    unsigned long long 	mlen,seek;
    AES_KEY         	enc_key;
    unsigned long long	i;
    unsigned char 		pub_seed_imt[params->n];
    unsigned long long	len;
    unsigned char		auth_node[imt_node_len];
    
    uint32_t 			imt_addr[8] = {0};
    			
    			
    memcpy(smd, sm, params->sig_bytes + XMSS_MLEN);
	memcpy(smd+params->sig_bytes + XMSS_MLEN, sm+2*(params->sig_bytes + params->pk_bytes) + XMSS_MLEN + 2*params->index_bytes+imt_tree_height*imt_node_len+params->n,AES_BLOCK_SIZE);	
	memcpy(smtd_pk,sm + params->sig_bytes + XMSS_MLEN, params->pk_bytes);
	printf("verify_dgmtU: Seq No: 1, Verification %d\n",xmssmt_core_sign_open_dgmt(params,mout,&mlen,smd,params->sig_bytes + XMSS_MLEN,smtd_pk));
		
	memcpy(smu, sm + params->sig_bytes + XMSS_MLEN + params->pk_bytes, params->sig_bytes);
	memcpy(smu + params->sig_bytes, sm + params->sig_bytes + XMSS_MLEN, params->n);
	
	memcpy(smtu_pk,sm + 2*params->sig_bytes + XMSS_MLEN + params->pk_bytes, params->pk_bytes);
	printf("verify_dgmtU: Seq No: 2, Verification %d\n",xmssmt_core_sign_open(params,mout,&mlen,smu,params->sig_bytes + XMSS_MLEN,smtu_pk));
	
	i0 = bytes_to_ull(sm + 2*(params->sig_bytes + params->pk_bytes) + XMSS_MLEN, params->index_bytes);
	i1 = bytes_to_ull(sm + 2*(params->sig_bytes + params->pk_bytes) + XMSS_MLEN + params->index_bytes, params->index_bytes);
	j  = bytes_to_ull(sm + params->sig_bytes + params->pk_bytes + XMSS_MLEN, params->index_bytes);
	
	       	
	if((fd_fk = open("./dgmmt/fallback/FallBackKeys", O_RDONLY, VERIFIER_PERMISSION))==-1){
    	printf("File: ./dgmmt/fallback/FallBackKeys open read error from verify_dgmtU\n");
    	exit(0);
    }else{
     	seek = ((internal_imt_nodes - (1 << (i0+1)) + i1 + 2)*SMT_PER_IMT_NODE+j);
        
        lseek(fd_fk, (2*AES_BLOCK_SIZE)*seek, SEEK_SET);
        if(read(fd_fk, fallbackkey, (2*AES_BLOCK_SIZE))!=(2*AES_BLOCK_SIZE)){
        	printf("File: ./dgmmt/fallback/FallBackKeys read error from verify_dgmtU\n");
        	exit(0);
        }else{
        	memset(imt_i0i1,0,imt_node_len);
			AES_set_encrypt_key(smtu_pk, 256, &enc_key);
			AES_encrypt(fallbackkey, imt_i0i1, &enc_key);
			AES_encrypt(fallbackkey+AES_BLOCK_SIZE, imt_i0i1+AES_BLOCK_SIZE, &enc_key);
			
			seek = (internal_imt_nodes - (1 << (i0+1)) + i1 + 2);
			
			printf("Fallback node checking = %d\n",memcmp(imt_i0i1,head[seek].value,imt_node_len));
        }
        close(fd_fk);
        
    }
    
    len = 2*(params->sig_bytes + params->pk_bytes) + XMSS_MLEN + 2*params->index_bytes+imt_tree_height*imt_node_len;
    memcpy(pub_seed_imt,sm+len,params->n);
    
    len = 2*(params->sig_bytes + params->pk_bytes) + XMSS_MLEN + 2*params->index_bytes;
    for(i=0; i<i0; i++){
    	memset(imt_addr,0,8*sizeof(uint32_t));
    	set_tree_height(imt_addr, i0-i-1);
    	set_tree_index(imt_addr, i1>>1);
    	
    	memcpy(auth_node,sm+len,imt_node_len); 	
    	if(i1 & 0x1){
    		thash_h_m(imt_params, imt_i0i1, auth_node, imt_i0i1, pub_seed_imt, imt_addr);	
        }else{
        	thash_h_m(imt_params, imt_i0i1, imt_i0i1, auth_node, pub_seed_imt, imt_addr);
        }	
        i1 = i1>>1;
        len = len + imt_node_len;        
    }
    
    printf("IMT root checking = %d\n",memcmp(imt_i0i1,head[(1<<(imt_tree_height+1))-2].value,imt_node_len));
 
}














