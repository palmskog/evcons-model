/***********************************************************************************
   NOTE: We have succesfully verified each function in isolation (which, of course,
    proves the whole program correct).
   Use VCC /m:<proc> to verify each procedure.
   VCC has problems verifying the code en bloc.
   Please perform verification in isolation or pass the option /z3opt:MBQI=true to VCC
    (the latter takes longer time).
   ************************************************************************************/


#include <vcc.h>
#include <stdlib.h>

#define HS_SIZE 0xffffff
#define PS_SIZE 0xffffff

/****************************************************************
The proof does _not_ depend on the number of nodes in the network, the number of keys stored,
 or the size of the preference list, which is the number of replicas storing the value of a key.
However, due to C array data-type limitations, we require VNODES * KEYS_NUM and VNODES*PREFLIST_SIZE
to not overflow. The constant values below limit the *maximum* number of nodes, keys, and preference-list
sizes, and the code simulates systems consisting of **all** configurations within the range of these values.
***************************************************************/


/***********************************************************************/
// Maximum number of nodes, keys, and preference-list sizes

#define VNODES        100000
#define KEYS_NUM      10000 
#define PREFLIST_SIZE 3200

/***********************************************************************/
// Configuration parameters: nondeterministically fixed
// keys_num - the number of keys in the store: ranges from 0 to KEYS_NUM 
// vnodes - the number of virtual nodes: ranges from 0 to VNODES
// preflist_size - the size of the preference list: ranges from 0 to PREFLIST_SIZE

typedef struct Configs {
	int keys_num;
	int vnodes;
	int preflist_size;
	_(invariant preflist_size > 0 && preflist_size <= PREFLIST_SIZE)
	_(invariant vnodes > 0 && vnodes <= VNODES)
	_(invariant keys_num > 0 && keys_num <= KEYS_NUM)
} Configs;
/************************************************************************/

#define SUCCESS 1

typedef int BOOL;
#define TRUE  1
#define FALSE 0

typedef struct LiveNodes {
	BOOL live_nodes[VNODES];
} LiveNodes;

/* ----- set of integers --------- */
_(ghost typedef \bool iset_t[int])
_(ghost _(pure) \integer card_iset(iset_t s)
	_(decreases 0))  	
_(ghost _(pure) iset_t empty_iset() 
 _(decreases 0)
 _(returns \lambda int i; \false))  
 _(axiom \forall int i; !empty_iset()[i])
_(ghost _(pure) iset_t addone_iset(iset_t s, int i) 
 _(decreases 0)
 _(returns \lambda int j; i == j ? \true : s[j]))  
_(ghost _(pure) iset_t delone_iset(iset_t s, int i) 
 _(decreases 0)
 _(returns \lambda int j; i == j ? \false : s[j])) 
 _(axiom \forall iset_t s; int i; addone_iset(delone_iset(s, i), i) == s)
_(axiom card_iset(empty_iset()) == 0) 
_(axiom \forall iset_t s; int i; card_iset(s) >= 0 && !s[i] ==> card_iset(addone_iset(s, i)) == card_iset(s) + 1)
_(axiom \forall iset_t s; int i; card_iset(s) >= 0 && s[i] ==> card_iset(addone_iset(s, i)) == card_iset(s))

_(axiom \forall iset_t s; int i; card_iset(s) >= 0 && s[i] ==> card_iset(delone_iset(s, i)) == card_iset(s) - 1) 

_(axiom \forall iset_t s; card_iset(s) == 0 ==> s == empty_iset())
_(axiom \forall iset_t s; {card_iset(s) } card_iset(s) >= 0)


// ****************************************************************************
// ****************************************************************************
_(pure)
int get_coord_for_key_new(int key, const int keys_num, const int vnodes)
	_(requires keys_num > 0 && vnodes > 0)
	_(requires key >= 0 && key < keys_num)
	_(ensures \result >= 0 && \result < vnodes) // && \result < (int)conf.vnodes)
	_(decreases 0)
{
	int result;
	_(assume result >= 0 && result < vnodes)
	return result;
}

typedef struct PreferenceLists {
	_(ghost int vals[int])

	// implementation
	int preference_list[VNODES * PREFLIST_SIZE];
	Configs conf;
	_(invariant \mine(&conf))

	_(invariant \forall int i; (i >= 0 && i < conf.vnodes * conf.preflist_size) 
		==> preference_list[i] >= 0 && preference_list[i] < conf.vnodes)

	// coupling invariant
	_(invariant \forall int i; 
		(i >= 0 && i < conf.vnodes * conf.preflist_size) ==> vals[i] == preference_list[i])
} PreferenceLists;


typedef struct LocalStores {
	// abstraction 
	_(ghost iset_t tainted_nodes)
	_(ghost int tainted_key)
	_(ghost \natural size)

	// implementation (concrete representation)
	int local_store[VNODES * KEYS_NUM];
	Configs conf;
	_(invariant \mine(&conf))
	size_t len;
	_(invariant len <= (size_t)(conf.vnodes * conf.keys_num))
	_(invariant tainted_key == -1 || tainted_key >= 0 && tainted_key < conf.keys_num)

} LocalStores;


typedef size_t Hint;

_(typedef _(record) struct AbsHint {
	\natural src;
	\natural dst;
	\natural key;
} AbsHint;)

/* ---------- set of hints ------------------ */
_(ghost typedef \bool hset_t[Hint])
_(ghost _(pure) \integer card_hset(hset_t s)
	_(decreases 0))  	
_(ghost _(pure) hset_t empty_hset() 
 _(decreases 0)
 _(returns \lambda Hint i; \false))  
_(ghost _(pure) hset_t addone_hset(hset_t s, Hint h) 
 _(decreases 0)
 _(returns \lambda Hint j; h == j ? \true : s[j]))  
_(ghost _(pure) hset_t delone_hset(hset_t s, Hint h) 
 _(decreases 0)
 _(returns \lambda Hint j; h == j ? \false : s[j])) 
 _(axiom \forall hset_t s; Hint i; addone_hset(delone_hset(s, i), i) == s)
_(axiom card_hset(empty_hset()) == 0) 
_(axiom \forall hset_t s; Hint i; card_hset(s) >= 0 && !s[i] ==> card_hset(addone_hset(s, i)) == card_hset(s) + 1)
_(axiom \forall hset_t s; Hint i; card_hset(s) >= 0 &&  s[i] ==> card_hset(delone_hset(s, i)) == card_hset(s) - 1) 


// ****************************************************************************

// ****************************************************************************
_(pure) 
Hint create_hint(int src, int dst, int key _(out AbsHint ah)) 
	_(requires src >= 0 && src < VNODES)
	_(requires dst >= 0 && dst < VNODES)
	_(requires key >= 0 && key < KEYS_NUM)
	_(ensures ah.src == (\natural)src)
	_(ensures ah.dst == (\natural)dst)
	_(ensures ah.key == (\natural)key)
	_(decreases 0)
{
	Hint src_result = (size_t)src;
	Hint dst_result = (size_t)dst;
	dst_result = dst_result;
	dst_result <<= 16; 
	Hint key_result = (size_t)key;
	key_result <<= 32;
	Hint result = key_result + dst_result + src_result; 
	_(ghost ah.src = (\natural)src)
	_(ghost ah.dst = (\natural)dst)
	_(ghost ah.key = (\natural)key)

	return result;
}

// ****************************************************************************

// ****************************************************************************
_(pure)
int get_dst(Hint h, int vnodes) 
	_(decreases 0)
	_(requires vnodes > 0 && vnodes <= VNODES)
	_(ensures \result >= 0)
	_(ensures \result < vnodes)
{
	return (int)((h >> 16) & (size_t)(vnodes-1));
}

// ****************************************************************************

// ****************************************************************************
_(pure)
int get_key(Hint h, int keys_num) 
	_(decreases 0)
	_(requires keys_num > 0 && keys_num <= KEYS_NUM)
	_(ensures \result >= 0)
	_(ensures \result < keys_num)
{
	return (int)((h >> 32) & (size_t)(keys_num-1));
}


typedef struct HintedHandoffStores {
	// abstraction
	_(ghost hset_t hset)
	_(ghost size_t idx[Hint])

	// tainted node abstraction
	_(ghost iset_t tainted_nodes)
	_(ghost int tkey)
	_(ghost int tcoord)

	// implementation
	Configs conf;
	_(invariant \mine(&conf))
	Hint hint_store[HS_SIZE]; 
	size_t size;
	_(invariant size <= HS_SIZE)

	_(invariant \forall size_t i; i < size ==> hset[hint_store[i]])
	_(invariant \forall Hint h; hset[h] ==> idx[h] < size)
	_(invariant \forall Hint h; hset[h] ==> hint_store[idx[h]] == h)

	_(invariant tkey >= 0 && tkey < conf.keys_num 
					==> tcoord >= 0 && tcoord < conf.vnodes)
} HintedHandoffStores;

typedef struct PendingSet {
	// abstraction
	_(ghost hset_t pset)
	_(ghost size_t idx[Hint])

	// tainted node abstraction
	_(ghost iset_t tainted_nodes)

	_(ghost int tkey)
	_(ghost int tcoord)

	// implementation
	Hint pending[PS_SIZE]; 
	size_t size;
	Configs conf;
	_(invariant \mine(&conf))
	_(invariant size <= PS_SIZE)

	_(invariant \forall size_t i; i < size ==> pset[pending[i]])
	_(invariant \forall Hint h; pset[h] ==> idx[h] < size)
	_(invariant \forall Hint h; pset[h] ==> pending[idx[h]] == h)

	_(invariant tkey >= 0 && tkey < conf.keys_num
					==> tcoord >= 0 && tcoord < conf.vnodes)
} PendingSet;



_(logic 
  \bool put_safety_check(int tainted_key, int tainted_coord, int pref_size, PreferenceLists *pl, LocalStores * ls, HintedHandoffStores *hhs, PendingSet * ps, int pl_size) = 
	tainted_key != -1 ==>
			(\forall int j; (j >= 0 && j < pref_size) 
				==> (ls->tainted_nodes[pl->preference_list[tainted_coord * pl_size + j]] 					
						|| ps->tainted_nodes[pl->preference_list[tainted_coord * pl_size + j]]
						|| hhs->tainted_nodes[pl->preference_list[tainted_coord * pl_size + j]])))

// ****************************************************************************

// ****************************************************************************
void init_live_nodes(LiveNodes  *ln, PreferenceLists *pl, LocalStores * ls)
	_(requires ln != NULL && pl != NULL && ls != NULL)
	_(writes \extent(ln))
	_(maintains \wrapped(pl) && \wrapped(ls))
	_(ensures \wrapped(ln))
	_(ensures pl->conf.vnodes == \old(pl->conf.vnodes))
	_(ensures pl->conf.keys_num == \old(pl->conf.keys_num))
	_(ensures pl->conf.preflist_size == \old(pl->conf.preflist_size))
	_(ensures ls->conf.keys_num == \old(ls->conf.keys_num))
	_(decreases 0)
{
	_(wrap ln)
}

_(logic 
  \bool consistent_conf(PreferenceLists * pl, Configs * conf) = 
	pl != NULL && conf != NULL ==>
		   conf->preflist_size == pl->conf.preflist_size
		&& conf->vnodes        == pl->conf.vnodes
		&& conf->keys_num      == pl->conf.keys_num)

_(logic 
\bool consistent_conf(LocalStores * ls, Configs * conf) = 
	ls != NULL && conf != NULL ==>
		   conf->preflist_size == ls->conf.preflist_size
		&& conf->vnodes        == ls->conf.vnodes
		&& conf->keys_num      == ls->conf.keys_num)

_(logic 
\bool consistent_conf(PendingSet * ps, Configs * conf) = 
	ps != NULL && conf != NULL ==>
		   conf->preflist_size == ps->conf.preflist_size
		&& conf->vnodes        == ps->conf.vnodes
		&& conf->keys_num      == ps->conf.keys_num)

// ****************************************************************************

// ****************************************************************************
void init_preference_lists(PreferenceLists * pl, Configs * conf) 
	_(requires pl != NULL)
	_(maintains \wrapped(conf))
	_(ensures conf->vnodes == \old(conf->vnodes))
	_(ensures conf->preflist_size == \old(conf->preflist_size))
	_(ensures conf->keys_num == \old(conf->keys_num))
	_(writes \extent(pl))
	_(ensures \wrapped(pl))
	_(ensures consistent_conf(pl, conf))
	_(decreases 0)
{
	int i = 0, j = 0;
	pl->conf.preflist_size = conf->preflist_size;
	pl->conf.vnodes = conf->vnodes;
	pl->conf.keys_num = conf->keys_num;
	while(i < pl->conf.vnodes) 
		_(invariant i >= 0 && i <= pl->conf.vnodes)
		_(invariant consistent_conf(pl, conf))
		_(invariant j == 0)
		_(invariant \forall int k; (k >= 0 && k < (i * pl->conf.preflist_size + j)) ==> pl->preference_list[k] >= 0 && pl->preference_list[k] < pl->conf.vnodes)
		_(invariant \forall int k; (k >= 0 && k < (i * pl->conf.preflist_size + j)) ==> pl->preference_list[k] == pl->vals[k])
		_(decreases VNODES - i)
	{
		_(assert i >= 0 && i < pl->conf.vnodes)
		int count = i;
		int value = 0;
		while(j < pl->conf.preflist_size)
			_(invariant consistent_conf(pl, conf))
			_(invariant i >= 0 && i < pl->conf.vnodes)
			_(invariant j >= 0 & j <= pl->conf.preflist_size)
			_(invariant count == i + j)
			_(invariant value >= 0 && value < pl->conf.vnodes)
			_(invariant \forall int k; (k >= 0 && k < (i * pl->conf.preflist_size + j)) ==> pl->preference_list[k] >= 0 && pl->preference_list[k] < pl->conf.vnodes)
			_(invariant \forall int k; (k >= 0 && k < (i * pl->conf.preflist_size + j)) ==> pl->preference_list[k] == pl->vals[k])
			_(decreases pl->conf.preflist_size - j)
		{
			int index = i * pl->conf.preflist_size + j;
			value = (count++ % pl->conf.vnodes);
			pl->preference_list[index] = value;
			_(ghost pl->vals[index] = value ;)
			j ++;
		}
		j = 0;
		i ++;
	}
	_(wrap &(pl->conf))
	_(wrap pl)
}


// ****************************************************************************

// ****************************************************************************
void init_local_stores(LocalStores * ls, Configs * conf, PreferenceLists * pl) 
	_(requires ls != NULL && pl != NULL)
	_(requires &(ls->conf) != &(pl->conf))
	_(maintains \wrapped(conf) && \wrapped(pl))
	//_(requires \extent_mutable(ls))
	_(writes \extent(ls))
	_(ensures \wrapped(ls))
	_(ensures ls->size == 0)
	_(ensures ls->tainted_key == -1)
	_(ensures consistent_conf(ls, conf))
	_(maintains consistent_conf(pl, conf))
	_(decreases 0)
{
	ls->conf.preflist_size = conf->preflist_size;
	ls->conf.vnodes = conf->vnodes;
	ls->conf.keys_num = conf->keys_num;

	int i = 0, j = 0;
	while(i < conf->vnodes) 
		_(invariant consistent_conf(ls, conf))
		_(invariant consistent_conf(pl, conf))
		_(invariant \wrapped(conf))
		_(invariant i <= conf->vnodes)
		_(invariant j == 0)
		_(invariant \forall int k; (k >= 0 && k < (i * conf->keys_num + j)) ==> ls->local_store[k] == -1)
	{
		while(j < conf->keys_num) 
			_(invariant consistent_conf(ls, conf))
			_(invariant consistent_conf(pl, conf))
			_(invariant \wrapped(conf))
			_(invariant i < conf->vnodes && j <= conf->keys_num)
			_(invariant \forall int k; (k >= 0 && k < (i * conf->keys_num + j)) ==> ls->local_store[k] == -1)
		{
			ls->local_store[i * conf->keys_num + j] = -1;
			j ++;
		}
		j = 0;
		i ++;
	}
	_(ghost ls->tainted_nodes = empty_iset())
	_(ghost ls->tainted_key = -1)
	ls->len = 0;
	_(ghost ls->size = 0)
	_(wrap &ls->conf)
	_(wrap ls)
}

// ****************************************************************************

// ****************************************************************************
void init_hinted_handoff_stores(HintedHandoffStores * hhs, PreferenceLists * pl, LocalStores * ls, Configs * conf) 
	_(requires hhs != NULL && pl != NULL && ls != NULL && conf != NULL)
	_(requires &(hhs->conf) != &(pl->conf))
	_(requires &(hhs->conf) != &(ls->conf))
	_(requires &(ls->conf) != &(pl->conf))

	_(maintains \wrapped(pl) && \wrapped(ls) && \wrapped(conf))
	_(requires \extent_mutable(hhs))
	_(writes \extent(hhs))
	_(ensures \wrapped(hhs))
	_(ensures hhs->size == 0)
	_(ensures hhs->hset == empty_hset())
	_(ensures pl->conf.vnodes == \old(pl->conf.vnodes))
	_(ensures pl->conf.keys_num == \old(pl->conf.keys_num))
	_(ensures pl->conf.preflist_size == \old(pl->conf.preflist_size))
	_(ensures ls->conf.keys_num == \old(ls->conf.keys_num))
	_(decreases 0)
{
	hhs->conf.preflist_size = conf->preflist_size;
	hhs->conf.vnodes = conf->vnodes;
	hhs->conf.keys_num = conf->keys_num;

	_(ghost hhs->tainted_nodes = empty_iset())
	_(ghost hhs->tkey   = -1;)
	_(ghost hhs->tcoord = -1;)
	_(ghost hhs->hset = empty_hset())
	hhs->size = 0;
	_(wrap &hhs->conf)
	_(wrap hhs)
}

// ****************************************************************************

// ****************************************************************************
void init_pending(PendingSet * ps, Configs * conf, PreferenceLists * pl, LocalStores * ls) 
	_(requires ps != NULL && pl != NULL && ls != NULL)
	_(maintains \wrapped(conf) && \wrapped(pl) && \wrapped(ls))
	_(requires \extent_mutable(ps))
	_(writes \extent(ps))
	_(ensures \wrapped(ps))
	_(ensures ps->size == 0)
	_(ensures ps->pset == empty_hset())
	_(ensures consistent_conf(ps, conf))
	_(ensures pl->conf.vnodes == \old(pl->conf.vnodes))
	_(ensures pl->conf.keys_num == \old(pl->conf.keys_num))
	_(ensures pl->conf.preflist_size == \old(pl->conf.preflist_size))
	_(ensures ls->conf.keys_num == \old(ls->conf.keys_num))
	_(decreases 0)
{
	ps->conf.preflist_size = conf->preflist_size;
	ps->conf.vnodes = conf->vnodes;
	ps->conf.keys_num = conf->keys_num;

	_(ghost ps->tainted_nodes = empty_iset())
	_(ghost ps->tkey   = -1;)
	_(ghost ps->tcoord = -1;)
	_(ghost ps->pset = empty_hset())
	ps->size = 0;
	_(wrap &ps->conf)
	_(wrap ps)
}

// ****************************************************************************

// ****************************************************************************
_(def)
void coord_times_plsize_lemma(int coord, int pl_size, const int vnodes) 
	_(requires coord >= 0 && coord < vnodes)
	_(requires pl_size > 0)
	_(ensures (coord * pl_size) + pl_size <= vnodes * pl_size) 
	_(decreases pl_size)
{ 
	if (pl_size == 1) return;
	coord_times_plsize_lemma(coord, pl_size - 1, vnodes); 	
}

// ****************************************************************************

// ****************************************************************************
int get(int key, int coord, BOOL is_tainted, LiveNodes * ln, PreferenceLists * pl, HintedHandoffStores * hhs, LocalStores * ls, PendingSet *ps, int RDT, Configs * conf) 
	_(maintains \wrapped(conf))
	_(maintains consistent_conf(pl, conf))
	_(maintains consistent_conf(ls, conf))
	_(requires coord >= 0 && coord < conf->vnodes)
	_(requires key >= 0 && key < conf->keys_num)
	_(requires ln != NULL && pl != NULL && hhs != NULL && ls != NULL)
	_(requires ln->live_nodes[get_coord_for_key_new(key, conf->keys_num, conf->vnodes)] == 1)
	_(reads \extent(pl))
	_(writes ln, ls, hhs, ps)
	_(maintains \wrapped(pl))
	_(maintains \wrapped(ln))
	_(maintains \wrapped(hhs))
	_(maintains \wrapped(ls))
	_(maintains \wrapped(ps))
	_(ensures is_tainted ==> (\forall int j; (j >= 0 && j < conf->preflist_size) 
						==> ls->tainted_nodes[pl->preference_list[coord * conf->preflist_size + j]]
							|| hhs->tainted_nodes[pl->preference_list[coord * conf->preflist_size + j]]
							|| ps->tainted_nodes[pl->preference_list[coord * conf->preflist_size + j]]))
{
	int cnt_succ = 0;
	int cur_node = -1;
	int i = 0;
	_(ghost coord_times_plsize_lemma(coord, conf->preflist_size, conf->vnodes))
	while(i < conf->preflist_size)
		_(invariant cnt_succ <= i)
		_(invariant \wrapped(pl) && \wrapped(ls) && \wrapped(ps) && \wrapped(hhs) && \wrapped(ln) && \wrapped(conf))
		_(invariant consistent_conf(pl, conf))
		_(invariant consistent_conf(ls, conf))
		_(writes ln, ls, ps, hhs)
		_(invariant i > 0 && is_tainted  && ln->live_nodes[cur_node] ==> ls->tainted_nodes[cur_node] || hhs->tainted_nodes[cur_node] || ps->tainted_nodes[cur_node])
		_(invariant i > 0 && is_tainted ==> (\forall int j; (j >= 0 && j < i) 
						==> ls->tainted_nodes[pl->preference_list[coord * conf->preflist_size + j]]
						    || hhs->tainted_nodes[pl->preference_list[coord * conf->preflist_size + j]]
							|| ps->tainted_nodes[pl->preference_list[coord * conf->preflist_size + j]] ))
	{
		_(assert consistent_conf(ls, conf))
		int index = coord * conf->preflist_size + i;
		cur_node = pl->preference_list[index];
		_(ghost coord_times_plsize_lemma(coord, conf->preflist_size, conf->vnodes))
		_(assert cur_node >= 0)
		if (ln->live_nodes[cur_node]) {
			cnt_succ ++;
		}
		i ++;
		_(assert consistent_conf(ls, conf))
		havoc_all(ln, ls, hhs, ps);
		_(ghost \state s0 = \now() ;)
		_(unwrap ls)
		_(ghost {
		if (is_tainted) { 			
			ls->tainted_key = key;
			ls->tainted_nodes =  addone_iset(ls->tainted_nodes, cur_node);
		}})
		_(wrap ls)
		_(assert guarantee(ls, hhs, ps, s0))
		havoc_all(ln, ls, hhs, ps);	
	}

	if (cnt_succ < RDT) return -1;
	return cnt_succ;
}

// ----------------------------------------------------------------------------
//                            STUB
// ----------------------------------------------------------------------------
_(pure)
BOOL write_succeeded()
	_(decreases 0) 
;

// ****************************************************************************

// ****************************************************************************
int put(int key, int coord, BOOL is_tainted, BOOL first_tainted_write, LiveNodes * ln, PreferenceLists * pl, LocalStores * ls, HintedHandoffStores * hhs, PendingSet *ps, int WDT, Configs * conf)
	_(maintains \wrapped(conf))
	_(requires key >= 0 && key < conf->keys_num)
	_(maintains ls->conf.keys_num == conf->keys_num)
	_(requires ps != NULL)
	_(maintains consistent_conf(pl, conf))
	_(maintains ps->conf.vnodes == conf->vnodes)
	_(maintains ps->conf.keys_num == conf->keys_num)
	_(maintains ps->conf.preflist_size == conf->preflist_size)
	_(requires coord >= 0 && coord < conf->vnodes)
	_(requires pl != NULL)
	_(requires ln->live_nodes[coord] == 1)
	_(requires ls != NULL)
	_(requires ps->size < UINT_MAX)
	_(requires !first_tainted_write ==> (\forall int j; (j >= 0 && j < conf->preflist_size) 
					==> (   ls->tainted_nodes[pl->preference_list[coord * conf->preflist_size + j]]
						     || ps->tainted_nodes[pl->preference_list[coord * conf->preflist_size + j]]
							 || hhs->tainted_nodes[pl->preference_list[coord * conf->preflist_size + j]]) ))

	_(maintains \wrapped(ln) && \wrapped(pl) && \wrapped(ls) && \wrapped(hhs) && \wrapped(ps))

	_(writes ln, ls, hhs, ps)

	_(ensures coord >= 0 && coord < conf->vnodes)
	_(ensures \result > -2 ==> ps->size <= PS_SIZE)
	_(ensures ps->size <= PS_SIZE)
	_(ensures hhs->size <= HS_SIZE)
	
	// basic safety invariant:
	_(ensures is_tainted && \result > -2 ==> put_safety_check(key, coord, conf->preflist_size, pl, ls, hhs, ps, conf->preflist_size))
	
	// invariant for all alive nodes:
	_(ensures is_tainted && \result > -2 
				==> (\forall int j; (j >= 0 && j < conf->preflist_size) 
					==> (   ls->tainted_nodes[pl->preference_list[coord * conf->preflist_size + j]]
						     || ps->tainted_nodes[pl->preference_list[coord * conf->preflist_size + j]]
							 || hhs->tainted_nodes[pl->preference_list[coord * conf->preflist_size + j]]) ))
	
	_(decreases 0)
{	
	
	_(ghost AbsHint abs_hint)
	int cnt_succ = 0;
	int cur_node = -1;
	int i = 0;
	_(ghost coord_times_plsize_lemma(coord, conf->preflist_size, conf->vnodes))
	while(i < conf->preflist_size) 
		_(invariant cnt_succ <= i)		
		_(invariant \wrapped(ln) && \wrapped(ls) && \wrapped(ps) && \wrapped(hhs))
		_(writes ln, ls, hhs, ps)
		_(invariant consistent_conf(pl, conf))
		//_(invariant consistent_conf(ls, conf))
		//_(invariant consistent_conf(ps, conf))
		_(invariant ps->size  <= PS_SIZE)	
		_(invariant hhs->size <= HS_SIZE)
		_(invariant coord >= 0 && coord < conf->vnodes)
		_(invariant ls->conf.keys_num == conf->keys_num)
		_(invariant ps->conf.vnodes == conf->vnodes)
		_(invariant ps->conf.keys_num == conf->keys_num)
		_(invariant ps->conf.preflist_size == conf->preflist_size)
		_(invariant i > 0 && is_tainted ==> ls->tainted_nodes[cur_node] || ps->tainted_nodes[cur_node] || hhs->tainted_nodes[cur_node])		
		_(invariant is_tainted  ==> put_safety_check(key, coord, i, pl, ls, hhs, ps, conf->preflist_size))
		
		_(invariant i > 0 && is_tainted  && ln->live_nodes[cur_node] && cnt_succ <= WDT ==> (ls->tainted_nodes[cur_node] || ps->tainted_nodes[cur_node] || hhs->tainted_nodes[cur_node]))
		
		_(invariant is_tainted 
					==> (\forall int j; (j >= 0 && j < i) 						 
							==> (   ls->tainted_nodes[pl->preference_list[coord * conf->preflist_size + j]]
								 || ps->tainted_nodes[pl->preference_list[coord * conf->preflist_size + j]]
								 || hhs->tainted_nodes[pl->preference_list[coord * conf->preflist_size + j]])))
	{
		_(assert \wrapped(conf))
		_(assert ps->conf.vnodes == conf->vnodes)
		int index_pl = coord * conf->preflist_size + i;
		cur_node = pl->preference_list[index_pl];
		_(assert cur_node >= 0)
		if (ln->live_nodes[cur_node] && cnt_succ < WDT) {		
			_(assert (i > 0 && is_tainted  && (! ln->live_nodes[cur_node] || cnt_succ >= WDT) && ps->size < PS_SIZE) ==> ps->tainted_nodes[cur_node])
			if (write_succeeded()) {
				havoc_all(ln, ls, hhs, ps);
				_(ghost \state s0 = \now() ;)
				_(unwrap ls)
				int index_ls = cur_node * conf->keys_num + key;
				ls->local_store[index_ls] = key;
				_(ghost { 					
					if (is_tainted) {
						ls->tainted_key = key;
						ls->tainted_nodes =  addone_iset(ls->tainted_nodes, cur_node);
						ls->size = ls->size + 1 ;
					}})
				_(wrap ls)
				_(assert guarantee(ls, hhs, ps, s0))
				havoc_all(ln, ls, hhs, ps);
				cnt_succ ++;
			} else {
				if (ps->size == PS_SIZE) { // *** run-time error: pending set is full *** 
					return -2;
				}
				havoc_all(ln, ls, hhs, ps);
				_(ghost \state s0 = \now() ;)
				_(unwrap ps)
					Hint h = create_hint(coord, cur_node, key _(out abs_hint));
					if(ps->size == PS_SIZE) {
						_(wrap ps)
						_(assert guarantee(ls, hhs, ps, s0))
						havoc_all(ln, ls, hhs, ps);
						return -2;
					}

					ps->pending[ps->size] = h;
					_(ghost ps->pset = addone_hset(ps->pset, h))
					_(ghost ps->idx[h] = ps->size)

					ps->size = ps->size + 1;


					_(ghost {
						if (is_tainted) {
							_(assert coord >= 0 && coord < conf->vnodes)
							if (ps->tkey == -1) {
								ps->tkey = key;
								ps->tcoord = coord;
							}
							ps->tainted_nodes = addone_iset(ps->tainted_nodes, cur_node);
				
					} })
				_(assert ps->conf.vnodes == conf->vnodes)
				_(wrap ps)
				_(assert guarantee(ls, hhs, ps, s0))
				havoc_all(ln, ls, hhs, ps);
			}
		} else { 
			_(assert ! ln->live_nodes[cur_node] || cnt_succ >= WDT)
			if (ps->size == PS_SIZE) // *** run-time error: pending set is full *** 
				return -2;

			_(assert (! ln->live_nodes[cur_node] || cnt_succ >= WDT) && ps->size < PS_SIZE)
			
			havoc_all(ln, ls, hhs, ps);
			_(ghost \state s0 = \now() ;)
			_(unwrap ps)
			if(ps->size == PS_SIZE) {
				_(wrap ps)
				_(assert guarantee(ls, hhs, ps, s0))
				havoc_all(ln, ls, hhs, ps);
				return -2;
			}

			_(ghost {
				if (is_tainted) {
					ps->tkey = key;
					ps->tcoord = coord;
					ps->tainted_nodes = addone_iset(ps->tainted_nodes, cur_node);
					_(assert ps->tainted_nodes[cur_node])
				} })
		
				Hint h = create_hint(coord, i, key _(out abs_hint));
				ps->pending[ps->size] = h;
				_(ghost ps->pset = addone_hset(ps->pset, h))
				_(ghost ps->idx[h] = ps->size)
				ps->size = ps->size + 1;
			_(assert ps->conf.vnodes == conf->vnodes)
			_(wrap ps)
			_(assert guarantee(ls, hhs, ps, s0))
			havoc_all(ln, ls, hhs, ps);			
		}
		i ++;
		_(assert \wrapped(conf))
	}
	if (cnt_succ < WDT) return -1;
	return cnt_succ;
}

// ----------------------------------------------------------------------------
//                            STUB
// ----------------------------------------------------------------------------
BOOL write_to_local_store()
	_(decreases 0)
	;

// ----------------------------------------------------------------------------
//                            STUB
// ----------------------------------------------------------------------------
BOOL write_to_slop_store()  // slop_store == hinted_handof_table
	_(decreases 0)
	;

// ----------------------------------------------------------------------------
//                            STUB
// ----------------------------------------------------------------------------
_(ghost
BOOL is_the_last_tainted(int key, int tainted_key, int tainted_coord, int dst_node, PendingSet *ps, Configs * conf) 
	_(requires conf != NULL)
	_(maintains \wrapped(conf))
	_(reads ps)
	_(requires tainted_coord == get_coord_for_key_new(tainted_key, conf->keys_num, conf->vnodes))
	_(decreases 0)
;)


// ****************************************************************************

// ****************************************************************************
void rm_pending_seq(int tainted_key, int tainted_coord, PreferenceLists *pl, HintedHandoffStores *hhs, LocalStores *ls, PendingSet *ps, Configs * conf) 
	_(requires pl != NULL && ls != NULL && hhs != NULL && ps != NULL)
	_(requires ps->size > 0)
	_(requires tainted_key >= 0 && tainted_key < conf->keys_num)
	_(requires tainted_key != -1 ==> tainted_coord == get_coord_for_key_new(tainted_key, conf->keys_num, conf->vnodes))
	_(requires hhs->size < HS_SIZE)
	_(maintains \wrapped(conf))
	_(maintains 
			(\forall int j; (j >= 0 && j < conf->preflist_size) 
				==> (ls->tainted_nodes[pl->preference_list[tainted_coord * conf->preflist_size + j]] 
					 || hhs->tainted_nodes[pl->preference_list[tainted_coord * conf->preflist_size + j]]
					 || ps->tainted_nodes[pl->preference_list[tainted_coord * conf->preflist_size + j]]))) 

	_(maintains \wrapped(hhs))
	_(maintains \wrapped(ls))
	_(maintains \wrapped(pl))
	_(maintains \wrapped(ps))

	_(reads \extent(pl))

	_(writes hhs)
	_(writes ls)
	_(writes ps)

	_(ensures ps->size == \old(ps->size) - 1)
	_(ensures hhs->size == \old(hhs->size) ||(hhs->size == \old(hhs->size) + 1))
	_(ensures hhs->size <= HS_SIZE)
	_(decreases ps->size)
{
	
	_(assert tainted_coord == get_coord_for_key_new(tainted_key, conf->keys_num, conf->vnodes))
	int x = tainted_coord * conf->preflist_size;

	Hint last_hint = ps->pending[ps->size-1];
	int dst_node = get_dst(last_hint, conf->vnodes);
	int key = get_key(last_hint, conf->keys_num);

	BOOL do_local_write = write_to_local_store();
	BOOL do_slop_write = write_to_slop_store();

	_(unwrap ps)
	_(unwrap ls)
	_(unwrap hhs)
	_(ghost {
		if (is_the_last_tainted(key, tainted_key, tainted_coord, dst_node, ps, conf)) {
			// delete from the abstract tainted store in the pending set
			ps->tainted_nodes = delone_iset(ps->tainted_nodes, dst_node); 

			if (do_local_write) { // write to the abstract tainted local store
				ls->tainted_nodes  = addone_iset(ls->tainted_nodes, dst_node);
				if (do_slop_write) {
					hhs->tainted_nodes = addone_iset(hhs->tainted_nodes, dst_node);
				}
			} else {
				hhs->tainted_nodes = addone_iset(hhs->tainted_nodes, dst_node);
			}
		} 
	})
	_(ghost ps->pset = \lambda Hint h; h == last_hint ? \false : ps->pset[h])
	_(assert addone_hset(delone_hset(ps->pset, last_hint), last_hint) == ps->pset) // *** hint for VCC ***

	_(assert addone_iset(delone_iset(ls->tainted_nodes, dst_node), dst_node) == ls->tainted_nodes) // *** hint for VCC ***
	_(assert addone_hset(delone_hset(hhs->hset, last_hint), last_hint) == hhs->hset) // *** hint for VCC ***

	// delete from the concrete pending set
	ps->pending[ps->size-1] = (size_t)-1;
	ps->size = ps->size - 1;
	_(wrap ps)

	if (do_local_write) {  // write to the concrete local store
		ls->local_store[dst_node *  conf->keys_num + key] = key;
		_(ghost ls->size = ls->size + 1 )
		if (do_slop_write) {
			hhs->hint_store[hhs->size] = last_hint;
			_(ghost hhs->hset = addone_hset(hhs->hset, last_hint))
			_(ghost hhs->idx[last_hint] = hhs->size)
			hhs->size = hhs->size + 1;
		}
	} else {
		hhs->hint_store[hhs->size] = last_hint;
		_(ghost hhs->hset = addone_hset(hhs->hset, last_hint))
		_(ghost hhs->idx[last_hint] = hhs->size)
		hhs->size = hhs->size + 1;
	}

	_(wrap hhs)
	_(wrap ls)
}

// ****************************************************************************

// ****************************************************************************
void rm_pending_rr(PreferenceLists *pl, LocalStores *ls, PendingSet *ps, Configs * conf) 
	_(requires pl != NULL && ls != NULL && ps != NULL && conf != NULL)
	_(requires ps->size > 0)
	_(maintains \wrapped(ls))
	_(maintains \wrapped(pl))
	_(maintains \wrapped(ps))
	_(maintains \wrapped(conf))
	_(writes ls)
	_(writes ps)
	_(ensures ps->size < \old(ps->size))
	_(decreases ps->size)
{

	Hint last_hint = ps->pending[ps->size-1];
	int dst_node = get_dst(last_hint, conf->vnodes);
	int key = get_key(last_hint, conf->keys_num);

	_(unwrap ps)
	_(unwrap ls)
	_(ghost ps->pset = \lambda Hint h; h == last_hint ? \false : ps->pset[h])
	_(assert addone_hset(delone_hset(ps->pset, last_hint), last_hint) == ps->pset) // *** hint for VCC ***

	// delete from the concrete pending set
	ps->pending[ps->size-1] = (size_t)-1;
	ps->size = ps->size - 1;
	_(wrap ps)

	ls->local_store[dst_node *  conf->keys_num + key] = key;
	_(wrap ls)
}

// ----------------------------------------------------------------------------
//                            STUB
// ----------------------------------------------------------------------------
void havoc_all(LiveNodes * ln, LocalStores *ls, HintedHandoffStores *hhs, PendingSet *ps)
	_(maintains \wrapped(ln) && \wrapped(ls) && \wrapped(hhs) && \wrapped(ps))
	_(writes ln, ls, hhs, ps)
	_(ensures \old(ls->tainted_key) != -1 ==> ls->tainted_key != -1)
	_(ensures \old(hhs->tkey) != -1 ==> hhs->tkey != -1)
	_(ensures \old(ps->tkey) != -1 ==> \old(ps->tkey) == ps->tkey)
	_(ensures ls->conf.vnodes == \old(ls->conf.vnodes))
	_(ensures ls->conf.keys_num == \old(ls->conf.keys_num))
	_(ensures ls->conf.preflist_size == \old(ls->conf.preflist_size))
	_(ensures ps->conf.vnodes == \old(ps->conf.vnodes))
	_(ensures ps->conf.keys_num == \old(ps->conf.keys_num))
	_(ensures ps->conf.preflist_size == \old(ps->conf.preflist_size))	
	_(ensures hhs->size >= 0 && hhs->size <= HS_SIZE )
	_(ensures ps->size >= 0 && ps->size <= PS_SIZE)
	_(ensures \forall int i; (\old(ls->tainted_nodes[i]) || \old(hhs->tainted_nodes[i]) || \old(ps->tainted_nodes[i])) 
								==>  (ls->tainted_nodes[i] || hhs->tainted_nodes[i] || ps->tainted_nodes[i]))
	_(decreases 0)
;

_(logic \bool guarantee(LocalStores *ls, HintedHandoffStores *hhs, PendingSet *ps, \state s0) = 
  		   \at(s0, ls->tainted_key) != -1 ==> ls->tainted_key != -1
		&& \at(s0, hhs->tkey) != -1 ==> hhs->tkey != -1
		&& \at(s0, ps->tkey) != -1 ==> ps->tkey != -1
		&& hhs->size >= 0 && hhs->size <= HS_SIZE 
		&& ps->size >= 0  && ps->size  <= PS_SIZE 
		&& \forall int i; (\at(s0, ls->tainted_nodes[i]) || \at(s0, hhs->tainted_nodes[i]) || \at(s0, ps->tainted_nodes[i])) 
						==>  (ls->tainted_nodes[i] || hhs->tainted_nodes[i] || ps->tainted_nodes[i])
  )

// ****************************************************************************

// ****************************************************************************
void rm_pending_conc(int tainted_key, int tainted_coord, LiveNodes * ln, PreferenceLists *pl, HintedHandoffStores *hhs, LocalStores *ls, PendingSet *ps, Configs * conf) 
	_(requires pl != NULL && ls != NULL && hhs != NULL && ps != NULL)
	_(requires ps->size >= 0)
	_(requires tainted_key >= 0 && tainted_key < conf->keys_num)
	_(requires tainted_key != -1 ==> tainted_coord == get_coord_for_key_new(tainted_key, conf->keys_num, conf->vnodes))
	_(requires hhs->size < HS_SIZE)

	_(maintains \wrapped(conf))
	_(maintains 
			(\forall int j; (j >= 0 && j < conf->preflist_size) 
				==> (ls->tainted_nodes[pl->preference_list[tainted_coord * conf->preflist_size + j]] 
					 || hhs->tainted_nodes[pl->preference_list[tainted_coord * conf->preflist_size + j]]
					 || ps->tainted_nodes[pl->preference_list[tainted_coord * conf->preflist_size + j]]))) 

	_(maintains \wrapped(hhs))
	_(maintains \wrapped(ls))
	_(maintains \wrapped(pl))
	_(maintains \wrapped(ps))
	_(maintains \wrapped(ln))

	_(reads \extent(pl))

	_(writes ln, ls, hhs, ps)

	_(decreases 0)
{
	
	_(assert tainted_coord == get_coord_for_key_new(tainted_key, conf->keys_num, conf->vnodes))
	int x = tainted_coord * conf->preflist_size;

	havoc_all(ln, ls, hhs, ps);
	_(ghost \state s0 = \now() ;)
	_(unwrap ps)
	if (ps->size == 0) {
		_(wrap ps)
		_(assert guarantee(ls, hhs, ps, s0))
		havoc_all(ln, ls, hhs, ps);
		return;
	}
	_(unwrap ls)
	_(unwrap hhs)

	Hint last_hint = ps->pending[ps->size-1];
	int dst_node = get_dst(last_hint, conf->vnodes);
	int key = get_key(last_hint, conf->keys_num);

	BOOL do_local_write = write_to_local_store();
	BOOL do_slop_write = write_to_slop_store();

	_(ghost {
	if (dst_node >= pl->preference_list[x] && dst_node <= pl->preference_list[x + (conf->preflist_size - 1)]) {
		// delete from the abstract tainted store in the pending set
		ps->tainted_nodes = delone_iset(ps->tainted_nodes, dst_node); 

		if (do_local_write) { // write to the abstract tainted local store
			ls->tainted_nodes  = addone_iset(ls->tainted_nodes, dst_node);
			if (do_slop_write) {
				hhs->tainted_nodes = addone_iset(hhs->tainted_nodes, dst_node);
			}
		} else {
			hhs->tainted_nodes = addone_iset(hhs->tainted_nodes, dst_node);
		}				
	} })


	_(ghost ps->pset = \lambda Hint h; h == last_hint ? \false : ps->pset[h])
	_(assert addone_hset(delone_hset(ps->pset, last_hint), last_hint) == ps->pset) // *** hint for VCC ***

	_(assert addone_iset(delone_iset(ls->tainted_nodes, dst_node), dst_node) == ls->tainted_nodes) // *** hint for VCC ***
	_(assert addone_hset(delone_hset(hhs->hset, last_hint), last_hint) == hhs->hset) // *** hint for VCC ***


	// delete from the concrete hint store
	ps->pending[ps->size-1] = (size_t)-1;
	ps->size = ps->size - 1;
	_(wrap ps)

	if (do_local_write) {  // write to the concrete local store
		ls->local_store[dst_node * conf->keys_num + key] = key;
		_(ghost ls->size = ls->size + 1 )
		if (do_slop_write) {
			_(assert hhs->size >= 0)
			if (hhs->size == HS_SIZE) {
				_(wrap hhs)
				_(wrap ls)
				_(assert guarantee(ls, hhs, ps, s0))
				havoc_all(ln, ls, hhs, ps);
				return;
			}
			hhs->hint_store[hhs->size] = last_hint;
			_(ghost hhs->hset = addone_hset(hhs->hset, last_hint))
			_(ghost hhs->idx[last_hint] = hhs->size)
			hhs->size = hhs->size + 1;
		}
	} else {
		if (hhs->size == HS_SIZE) {
			_(wrap hhs)
			_(wrap ls)
			_(assert guarantee(ls, hhs, ps, s0))
			havoc_all(ln, ls, hhs, ps);
			return;
		}
		hhs->hint_store[hhs->size] = last_hint;
		_(ghost hhs->hset = addone_hset(hhs->hset, last_hint))
		_(ghost hhs->idx[last_hint] = hhs->size)
		hhs->size = hhs->size + 1;
	}

	_(wrap hhs)
	_(wrap ls)
	_(assert guarantee(ls, hhs, ps, s0))
	havoc_all(ln, ls, hhs, ps);

}
					
// ****************************************************************************

// ****************************************************************************
void handoff_hint_conc(int tainted_key, int tainted_coord, LiveNodes *ln, PreferenceLists *pl, HintedHandoffStores *hhs, LocalStores *ls, PendingSet * ps, Configs * conf) 
	_(requires pl != NULL && ls != NULL && hhs != NULL)
	_(requires hhs->size >= 0)
	_(requires tainted_key >= 0 && tainted_key <  conf->keys_num)
	_(requires tainted_key != -1 ==> tainted_coord == get_coord_for_key_new(tainted_key, conf->keys_num, conf->vnodes))
	_(maintains \wrapped(conf))
	_(maintains (\forall int j; (j >= 0 && j < conf->preflist_size) 
				==> (ls->tainted_nodes[pl->preference_list[tainted_coord * conf->preflist_size + j]] 
						|| hhs->tainted_nodes[pl->preference_list[tainted_coord * conf->preflist_size + j]]
						|| ps->tainted_nodes[pl->preference_list[tainted_coord * conf->preflist_size + j]])))

	_(maintains \wrapped(ln) && \wrapped(pl) && \wrapped(ls) && \wrapped(hhs) && \wrapped(ps))
	_(reads \extent(pl))
	_(writes ln, ls, hhs, ps)
	_(decreases 0)
{
	
	_(assert tainted_coord == get_coord_for_key_new(tainted_key, conf->keys_num, conf->vnodes))
	int x = tainted_coord * conf->preflist_size;
	havoc_all(ln, ls, hhs, ps);
	_(ghost \state s0 = \now() ;)
	_(unwrap hhs)
	// this is required because other threads can concurrently remove the hints
	if (hhs->size == 0) {
		_(wrap hhs)
		_(assert guarantee(ls, hhs, ps, s0))
		havoc_all(ln, ls, hhs, ps);
		return;
	}
	
	Hint last_hint = hhs->hint_store[hhs->size-1];
	int dst_node = get_dst(last_hint, conf->vnodes);
	int key = get_key(last_hint, conf->keys_num);

	_(unwrap ls)
	_(ghost {
	if (dst_node >= pl->preference_list[x] && dst_node <= pl->preference_list[x + (conf->preflist_size - 1)]) {
		// write to the abstract tainted hinted handoff store
		hhs->tainted_nodes = delone_iset(hhs->tainted_nodes, dst_node); 
		// delete from the abstract tainted store
		ls->tainted_nodes  = addone_iset(ls->tainted_nodes, dst_node);		
	} })
	_(ghost hhs->hset = \lambda Hint h; h == last_hint ? \false : hhs->hset[h])
	_(assert addone_hset(delone_hset(hhs->hset, last_hint), last_hint) == hhs->hset) // *** hint for VCC ***
	_(assert addone_iset(delone_iset(ls->tainted_nodes, dst_node), dst_node) == ls->tainted_nodes) // *** hint for VCC ***

	// delete from the concrete hint store
	hhs->hint_store[hhs->size - 1] = (size_t)-1;
	hhs->size = hhs->size - 1;

	// write to the concrete local store
	ls->local_store[dst_node * conf->keys_num + key] = key;
	_(ghost ls->size = ls->size + 1 ;)
	_(wrap hhs)
	_(wrap ls)
	_(assert guarantee(ls, hhs, ps, s0))
	havoc_all(ln, ls, hhs, ps);
}

// ****************************************************************************

// ****************************************************************************
void handoff_hint_seq(int tainted_key, int tainted_coord, PreferenceLists *pl, HintedHandoffStores *hhs, LocalStores *ls, PendingSet * ps, Configs * conf) 
	_(requires pl != NULL && ls != NULL && hhs != NULL)
	_(requires hhs->size > 0)
	_(requires tainted_key >= 0 && tainted_key < conf->keys_num)
	_(requires tainted_key != -1 ==> tainted_coord == get_coord_for_key_new(tainted_key, conf->keys_num, conf->vnodes))
	_(maintains \wrapped(conf))
	_(maintains (\forall int j; (j >= 0 && j < conf->preflist_size) 
				==> (ls->tainted_nodes[pl->preference_list[tainted_coord * conf->preflist_size + j]] 
						|| hhs->tainted_nodes[pl->preference_list[tainted_coord * conf->preflist_size + j]]
						|| ps->tainted_nodes[pl->preference_list[tainted_coord * conf->preflist_size + j]])))
	_(maintains \wrapped(hhs))
	_(maintains \wrapped(ls))
	_(maintains \wrapped(pl))
	_(maintains \wrapped(ps))
	_(reads \extent(pl))
	_(writes hhs)
	_(writes ls)
	_(ensures hhs->size < \old(hhs->size))
	_(ensures ps->size == \old(ps->size))
	_(decreases hhs->size)
{
	
	_(assert tainted_coord == get_coord_for_key_new(tainted_key, conf->keys_num, conf->vnodes))
	int x = tainted_coord * conf->preflist_size;
	Hint last_hint = hhs->hint_store[hhs->size-1];
	int dst_node = get_dst(last_hint, conf->vnodes);
	int key = get_key(last_hint, conf->keys_num);

	_(unwrap hhs)
	_(unwrap ls)
	_(ghost {
	if (dst_node >= pl->preference_list[x] && dst_node <= pl->preference_list[x + (conf->preflist_size - 1)]) {
		// write to the abstract tainted hinted handoff store
		hhs->tainted_nodes = delone_iset(hhs->tainted_nodes, dst_node); 
		// delete from the abstract tainted store
		ls->tainted_nodes  = addone_iset(ls->tainted_nodes, dst_node);
	} })
	_(ghost hhs->hset = \lambda Hint h; h == last_hint ? \false : hhs->hset[h])
	_(assert addone_hset(delone_hset(hhs->hset, last_hint), last_hint) == hhs->hset) // *** hint for VCC ***
	_(assert addone_iset(delone_iset(ls->tainted_nodes, dst_node), dst_node) == ls->tainted_nodes) // *** hint for VCC ***

	// delete from the concrete hint store
	hhs->hint_store[hhs->size-1] = (size_t)-1;
	hhs->size = hhs->size - 1;

	// write to the concrete local store
	ls->local_store[dst_node * conf->keys_num + key] = key;
	_(ghost ls->size = ls->size + 1 ;)
	_(wrap hhs)
	_(wrap ls)
}

// ****************************************************************************

// ****************************************************************************
_(pure)
BOOL get_arbitrary_bool() 
	_(ensures \result == TRUE || \result == FALSE)
	_(decreases 0)
{
	// IMPLEMENTATION: use random() implementation for an executable
	BOOL ret;
	_(assume ret == TRUE || ret == FALSE)
	return ret;
}


// ****************************************************************************

// ****************************************************************************
_(pure)
int get_arbitrary_num_in_range(int low, int high) 
	_(requires high > low)
	_(ensures \result >= low && \result < high)
	_(decreases 0)
{
	int ret;
	_(assume ret >= low && ret < high)
	// IMPLEMENTATION: use random() implementation for an executable
	return ret;
}


// ****************************************************************************

// ****************************************************************************
void get_alive_coordinator(LiveNodes * ln, int coord, Configs * conf, PreferenceLists * pl, PendingSet * ps, LocalStores * ls) 
	_(requires coord >= 0 && coord < conf->vnodes)
	_(maintains \wrapped(ln) && \wrapped(conf))
	_(maintains \wrapped(pl) && \wrapped(ps) && \wrapped(ls))
	_(writes ln)
	_(ensures ln->live_nodes[coord] == TRUE)
	_(ensures conf->vnodes == \old(conf->vnodes))
	_(ensures conf->keys_num == \old(conf->keys_num))
	_(ensures conf->preflist_size == \old(conf->preflist_size))
	_(maintains pl->conf.vnodes == conf->vnodes)
	_(maintains pl->conf.keys_num == conf->keys_num)
	_(maintains pl->conf.preflist_size == conf->preflist_size)
	_(ensures ps->conf.vnodes == \old(ps->conf.vnodes))
	_(ensures ps->conf.keys_num == \old(ps->conf.keys_num))
	_(ensures ps->conf.preflist_size == \old(ps->conf.preflist_size))
	_(ensures ls->conf.keys_num == \old(ls->conf.keys_num))

	_(decreases 0)
{
	_(unwrap ln)
	ln->live_nodes[coord] = TRUE;
	_(wrap ln)
}

// ****************************************************************************

// ****************************************************************************
void nodes_fail_and_recover_arbitrarily(LiveNodes *ln, Configs * conf, PreferenceLists * pl, PendingSet * ps, LocalStores *ls)  
	_(maintains \wrapped(ln))
	_(maintains \wrapped(conf) && \wrapped(pl) && \wrapped(ps) && \wrapped(ls))
	_(writes ln)
	_(ensures \forall int i;  (i >= 0 && i < conf->vnodes) ==> (ln->live_nodes[i] == TRUE || ln->live_nodes[i] == FALSE))
	_(ensures conf->vnodes == \old(conf->vnodes))
	_(ensures conf->keys_num == \old(conf->keys_num))
	_(ensures conf->preflist_size == \old(conf->preflist_size))
	_(ensures pl->conf.vnodes == \old(pl->conf.vnodes))
	_(ensures pl->conf.keys_num == \old(pl->conf.keys_num))
	_(ensures pl->conf.preflist_size == \old(pl->conf.preflist_size))
	_(ensures ps->conf.vnodes == \old(ps->conf.vnodes))
	_(ensures ps->conf.keys_num == \old(ps->conf.keys_num))
	_(ensures ps->conf.preflist_size == \old(ps->conf.preflist_size))
	_(ensures ls->conf.keys_num == \old(ls->conf.keys_num))

	_(decreases 0)
{
	for(int i = 0; i < conf->vnodes; i++) 
		_(writes ln)
		_(invariant \wrapped(ln))
		_(invariant pl->conf.vnodes == \old(pl->conf.vnodes))
		_(invariant pl->conf.keys_num == \old(pl->conf.keys_num))
		_(invariant pl->conf.preflist_size == \old(pl->conf.preflist_size))
		_(invariant ps->conf.vnodes == \old(ps->conf.vnodes))
		_(invariant ps->conf.keys_num == \old(ps->conf.keys_num))
		_(invariant ps->conf.preflist_size == \old(ps->conf.preflist_size))
		_(invariant \wrapped(conf))
		_(invariant \forall int j;  (j >= 0 && j < i) ==> (ln->live_nodes[j] == TRUE || ln->live_nodes[j] == FALSE))
	{
		_(unwrap ln)
		ln->live_nodes[i] = get_arbitrary_bool();
		_(wrap ln)
	}
}

// ****************************************************************************

// ****************************************************************************
void all_nodes_recover(LiveNodes * ln, Configs * conf)  
	_(maintains \wrapped(ln))
	_(maintains \wrapped(conf))
	_(writes ln)
	_(ensures \forall int i;  (i >= 0 && i < conf->vnodes) ==> ln->live_nodes[i] == TRUE)
	_(decreases 0)
{
	for(int i = 0; i < conf->vnodes; i++) 
		_(writes ln)
		_(invariant \wrapped(ln))
		_(invariant \forall int j;  (j >= 0 && j < i) ==> ln->live_nodes[j] == TRUE)
	{
		_(unwrap ln)
		ln->live_nodes[i] = TRUE;
		_(wrap ln)
	}
}

// ****************************************************************************

// ****************************************************************************
void empty_hhs_ps(PreferenceLists * pl, HintedHandoffStores * hhs, LocalStores * ls, PendingSet * ps, int tainted_key, int tainted_coord, int tmp_coord, Configs * conf) 
		_(maintains \wrapped(pl) && \wrapped(hhs) && \wrapped(ls) && \wrapped(ps) && \wrapped(conf))
		_(requires tainted_key >= 0 && tainted_key < conf->keys_num)
		_(requires tainted_coord == get_coord_for_key_new(tainted_key, conf->keys_num, conf->vnodes))
		_(requires tmp_coord == tainted_coord * conf->preflist_size)
		_(maintains (\forall int j; (j >= 0 && j < conf->preflist_size) ==>
							(ls->tainted_nodes[pl->preference_list[tmp_coord + j]] 
							|| hhs->tainted_nodes[pl->preference_list[tmp_coord + j]]
							|| ps->tainted_nodes[pl->preference_list[tmp_coord + j]])))
		_(writes hhs, ls, ps)
		_(ensures hhs->size == 0)
		_(ensures ps->size == 0)

		_(decreases 0)
		
{
  // LIVENESS 2 * ps + hinted store -> 
		while(hhs->size > 0 || ps->size > 0) 
			_(invariant hhs->size >= 0 && hhs->size <= HS_SIZE)
			_(invariant ps->size >= 0 && ps->size <= PS_SIZE)
			_(invariant \wrapped(hhs) && \wrapped(ls) && \wrapped(ps) && \wrapped(conf))
			_(invariant tainted_coord == get_coord_for_key_new(tainted_key, conf->keys_num, conf->vnodes))
			_(invariant (\forall int j; (j >= 0 && j < conf->preflist_size) ==>
							(ls->tainted_nodes[pl->preference_list[tmp_coord + j]] 
							|| hhs->tainted_nodes[pl->preference_list[tmp_coord + j]]
							|| ps->tainted_nodes[pl->preference_list[tmp_coord + j]])))

			_(writes hhs, ls, ps)
			_(decreases hhs->size + 2 * ps->size)
	{	
		_(ghost \state s0 = \now() ;)
		if (hhs->size > 0 && ps->size <= 0) {
			handoff_hint_seq(tainted_key, tainted_coord, pl, hhs, ls, ps, conf);
			_(assert (hhs->size < \at(s0, hhs->size) && ps->size <= \at(s0, ps->size)))
		} else if (hhs->size <= 0 && ps->size > 0) {
			_(assume hhs->size < HS_SIZE);
			rm_pending_seq(tainted_key, tainted_coord, pl, hhs, ls, ps, conf);
			_(assert (ps->size < \at(s0, ps->size) && hhs->size <= \at(s0, hhs->size) + 1))
		}
		else {
			if (star()) {
				handoff_hint_seq(tainted_key, tainted_coord, pl, hhs, ls, ps, conf);
				_(assert (hhs->size < \at(s0, hhs->size) && ps->size <= \at(s0, ps->size)))
			} else {
				_(assume hhs->size < HS_SIZE);
				rm_pending_seq(tainted_key, tainted_coord, pl, hhs, ls, ps, conf);
				_(assert (ps->size < \at(s0, ps->size) && hhs->size <= \at(s0, hhs->size) + 1))
			}
		} 
	}
}

// ----------------------------------------------------------------------------
//                            STUB
// ----------------------------------------------------------------------------
void permute_ps_idx(PendingSet *ps)
	_(maintains ps->size <= PS_SIZE)
	_(maintains \wrapped(ps))
	_(writes ps)
	_(ensures \forall Hint h; ps->pset[h] == \old(ps->pset[h]))
	_(ensures \forall int i; ps->tainted_nodes[i] == \old(ps->tainted_nodes[i]))
	_(ensures ps->size == \old(ps->size))
	_(ensures ps->tkey == \old(ps->tkey))
	_(ensures ps->tcoord == \old(ps->tcoord))
	_(ensures \wrapped(ps))
	_(decreases 0)
;

// ----------------------------------------------------------------------------
//                            STUB
// ----------------------------------------------------------------------------
void permute_hhs_idx(HintedHandoffStores *hhs)
	_(maintains hhs->size <= HS_SIZE)
	_(maintains \wrapped(hhs))
	_(writes hhs)
	_(ensures \forall Hint h; hhs->hset[h] == \old(hhs->hset[h]))
	_(ensures \forall int i; hhs->tainted_nodes[i] == \old(hhs->tainted_nodes[i]))
	_(ensures hhs->size == \old(hhs->size))
	_(ensures hhs->tkey == \old(hhs->tkey))
	_(ensures hhs->tcoord == \old(hhs->tcoord))
	_(ensures \wrapped(hhs))
	_(decreases 0)
;

// ****************************************************************************

// ****************************************************************************
int harness(LiveNodes * ln, PreferenceLists * pl, HintedHandoffStores * hhs, LocalStores * ls, PendingSet * ps, int WDT, Configs * conf _(out int tkey) _(out int tcoord))
	_(requires \wrapped(conf))
	_(requires &(pl->conf) != &(ls->conf))
	_(requires &(pl->conf.vnodes) != &(ls->conf.vnodes))
	_(requires &(pl->conf) != &(ps->conf))
	_(requires &(ls->conf) != &(ps->conf))
	_(requires &(hhs->conf) != &(ps->conf))
	_(requires &(hhs->conf) != &(pl->conf))
	_(requires &(hhs->conf) != &(ls->conf))
	_(requires WDT >= 0 && WDT < INT_MAX)
	_(requires conf != NULL && pl != NULL && ls != NULL && hhs != NULL && ps != NULL)
	_(requires hhs->size < HS_SIZE)
	_(requires ps->size < PS_SIZE)
	_(writes ln)
	_(writes \extent(pl))
	_(writes \extent(ln), \extent(hhs), \extent(ls), \extent(ps))
	_(writes \extent(ls))
	_(ensures \wrapped(pl) && \wrapped(ls) && \wrapped(hhs))
	_(ensures \wrapped(ps))
	_(decreases hhs->size)
{
	init_preference_lists(pl, conf);
	init_local_stores(ls, conf, pl);
	init_hinted_handoff_stores(hhs, pl, ls, conf);
	init_live_nodes(ln, pl, ls);
	init_pending(ps, conf, pl, ls);

	int tainted_key = -1;
	int tainted_coord = -1;
	BOOL tainted_key_set = FALSE;
	int lo = 10;
	int hi = 1000;
	int num_rounds = get_arbitrary_num_in_range(lo, hi);
	_(assert ls->tainted_key == -1)
	while(num_rounds > 0)
		_(invariant \wrapped(ls))
		_(invariant \wrapped(hhs))
		_(invariant \wrapped(ps))
		_(invariant \wrapped(ln))
		_(invariant \wrapped(conf))
		_(invariant consistent_conf(ps, conf))
		_(invariant consistent_conf(pl, conf))
		_(invariant ls->conf.keys_num == conf->keys_num)
		_(invariant num_rounds >= 0 && num_rounds <= 1000)
		_(invariant hhs->size >= 0 && hhs->size <= HS_SIZE)
		_(invariant ps->size >= 0 && ps->size < PS_SIZE)
		//_(invariant tainted_coord < conf->vnodes)
		_(invariant tainted_key_set ==> tainted_key >= 0 && tainted_key < conf->keys_num)
		_(invariant tainted_key != -1 && tainted_coord == get_coord_for_key_new(tainted_key, conf->keys_num, conf->vnodes)
					==> (\forall int j; (j >= 0 && j < conf->preflist_size) 
						==> (ls->tainted_nodes[pl->preference_list[tainted_coord * conf->preflist_size + j]] 
							|| hhs->tainted_nodes[pl->preference_list[tainted_coord * conf->preflist_size + j]]
							|| ps->tainted_nodes[pl->preference_list[tainted_coord * conf->preflist_size + j]]) ))
		_(invariant tainted_key_set ==> tainted_key != -1 && tainted_coord == get_coord_for_key_new(tainted_key, conf->keys_num, conf->vnodes))
		_(invariant tainted_key != -1 ==> tainted_coord == get_coord_for_key_new(tainted_key, conf->keys_num, conf->vnodes))
		_(writes ls)
		_(writes hhs)
		_(writes ps)
		_(writes ln)
		_(decreases num_rounds)
	{

		if (!tainted_key_set) {
			tainted_key = get_arbitrary_num_in_range(0, conf->keys_num);
			tainted_coord = get_coord_for_key_new(tainted_key, conf->keys_num, conf->vnodes);
			get_alive_coordinator(ln, tainted_coord, conf, pl, ps, ls);
			int ret_put = put(tainted_key, tainted_coord, TRUE, TRUE,  ln, pl, ls, hhs, ps, WDT, conf);

			if (ret_put >= WDT) {
				tainted_key_set = TRUE;
			} else {
				tainted_key = -1;
			}
		}


		if(ps->size == PS_SIZE) {
			return -1;
		}
		nodes_fail_and_recover_arbitrarily(ln, conf, pl, ps, ls);
		num_rounds --;
	}

	if (!tainted_key_set) {
		return -1;
	}

	_(assert hhs->size >= 0 && hhs->size <= HS_SIZE)
	_(assert tainted_key >= 0 && tainted_key < conf->keys_num)
	
	_(assert tainted_key_set ==> tainted_key != -1 && tainted_coord == get_coord_for_key_new(tainted_key, conf->keys_num, conf->vnodes))
	// ============================== SAFETY CHECK ===========================================
	_(assert (\forall int j; (j >= 0 && j < conf->preflist_size) 
				==> (ls->tainted_nodes[pl->preference_list[tainted_coord * conf->preflist_size + j]] 
					|| hhs->tainted_nodes[pl->preference_list[tainted_coord * conf->preflist_size + j]]
					|| ps->tainted_nodes[pl->preference_list[tainted_coord * conf->preflist_size + j]]) ))
	

	all_nodes_recover(ln, conf);
	permute_ps_idx(ps);
	permute_hhs_idx(hhs);

	int tmp_coord = tainted_coord * conf->preflist_size;

	_(assert tainted_key_set ==> tainted_key != -1 && tainted_coord == get_coord_for_key_new(tainted_key, conf->keys_num, conf->vnodes))	
	// ============================== SAFETY CHECK ===========================================
	_(assert (\forall int j; (j >= 0 && j < conf->preflist_size) ==>
							(ls->tainted_nodes[pl->preference_list[tmp_coord + j]] 
							|| hhs->tainted_nodes[pl->preference_list[tmp_coord + j]]
							|| ps->tainted_nodes[pl->preference_list[tmp_coord + j]])))

	// ================= LIVENESS ===========
	// ======== EVENTUAL CONSISTENCY ========
	empty_hhs_ps(pl, hhs, ls, ps, tainted_key, tainted_coord, tmp_coord, conf);

	// ============================== SAFETY CHECK ===========================================
	_(assert (\forall int j; (j >= 0 && j < conf->preflist_size) ==>
							(ls->tainted_nodes[pl->preference_list[tmp_coord + j]] 
							|| (hhs->tainted_nodes[pl->preference_list[tmp_coord + j]] && hhs->size == 0)
							|| (ps->tainted_nodes[pl->preference_list[tmp_coord + j]] && ps->size == 0))))

	return SUCCESS;
}

// ----------------------------------------------------------------------------
//                            STUB
// ----------------------------------------------------------------------------
_(pure)
BOOL star()
	_(decreases 0)
;

// ----------------------------------------------------------------------------
//                            STUB
// ----------------------------------------------------------------------------
int merge(int val, int value)
	_(decreases 0)
;

// ****************************************************************************

// ****************************************************************************
int harness_read_repair_aux(int key, int coord, LiveNodes * ln, PreferenceLists * pl, HintedHandoffStores * hhs, LocalStores * ls, PendingSet * ps, Configs * conf, int val, int consistent, int cur_node) 
	_(requires pl != NULL && ls != NULL && hhs != NULL)
	_(requires coord >= 0 && coord < conf->vnodes)
	_(requires key >= 0 && key < conf->keys_num)
	_(requires ps->size < PS_SIZE)
	_(requires ps->size >= 0)
	_(requires consistent == TRUE ==> \forall int j; (j >= 0 && j < conf->preflist_size) ==> ls->local_store[pl->preference_list[coord * conf->preflist_size + j]] == val)

	_(maintains \wrapped(ln))
	_(maintains \wrapped(hhs))
	_(maintains \wrapped(ls))
	_(maintains \wrapped(ps))
	_(maintains \wrapped(pl))
	_(maintains \wrapped(conf))
	_(maintains consistent_conf(pl, conf))
	_(writes ls)
	_(writes ps)
	_(writes hhs)
	_(ensures \result == TRUE ==> \forall int j; (j >= 0 && j < conf->preflist_size) ==> ls->local_store[pl->preference_list[coord * conf->preflist_size + j]] == val)
	_(ensures ps->size < \old(ps->size) || (ps->size == \old(ps->size) && \result == TRUE))
	_(decreases 0)
{
	consistent = TRUE;
	int i = 0;
	while(i < conf->preflist_size) 
		_(decreases conf->preflist_size - i)
		_(writes ls)
		_(writes ps)
		_(invariant \wrapped(ln))
		_(invariant \wrapped(ls))
		_(invariant \wrapped(ps))
		_(invariant \wrapped(pl))
		_(invariant \wrapped(conf))
		_(invariant i >= 0 && i <= conf->preflist_size)
		_(invariant consistent_conf(pl, conf))
		_(invariant ps->size < PS_SIZE)
		_(invariant i > 0 ==> cur_node >= 0 && cur_node < conf->vnodes)
		_(invariant consistent == TRUE ==> \forall int j; (j >= 0 && j < i) ==> ls->local_store[pl->preference_list[coord * conf->preflist_size + j]] == val)
		_(invariant ps->size < \old(ps->size) || (ps->size == \old(ps->size) && consistent == TRUE))
	{
		int index = coord * conf->preflist_size + i;
		cur_node = pl->preference_list[index];
		_(ghost coord_times_plsize_lemma(coord, conf->preflist_size, conf->vnodes))
		if(star() && ps->size > 0) 
		{
			rm_pending_rr(pl, ls, ps, conf);
			consistent = FALSE;
		}

		_(unwrap ls)
		ls->local_store[cur_node] = val;
		_(wrap ls)

		if(star() && ps->size > 0) {
			rm_pending_rr(pl, ls, ps, conf);
			consistent = FALSE;
		}
		i ++;
	}
	return consistent;
}

// ****************************************************************************

// ****************************************************************************
void harness_read_repair(int key, int coord, LiveNodes * ln, PreferenceLists * pl, HintedHandoffStores * hhs, LocalStores * ls, PendingSet * ps, Configs * conf) 
	_(requires pl != NULL && ls != NULL && hhs != NULL)
	_(requires coord >= 0 && coord < conf->vnodes)
	_(requires key >= 0 && key < conf->keys_num)
	_(requires hhs->size < HS_SIZE)
	_(requires ps->size < PS_SIZE)
	_(requires ps->size >= 0)
	_(maintains \wrapped(ln))
	_(maintains \wrapped(hhs))
	_(maintains \wrapped(ls))
	_(maintains \wrapped(ps))
	_(maintains \wrapped(pl))
	_(maintains \wrapped(conf))
	_(maintains consistent_conf(pl, conf))
	_(writes ls)
	_(writes ps)
	_(writes hhs)

	_(decreases 0)
{
	BOOL consistent = FALSE;
	int cur_node;
	int i = 0;
	int val;
	_(ghost coord_times_plsize_lemma(coord, conf->preflist_size, conf->vnodes))
	while(consistent == FALSE) 
		_(decreases ps->size)
		_(invariant \wrapped(ln))
		_(invariant \wrapped(hhs))
		_(invariant \wrapped(ls))
		_(invariant \wrapped(ps))
		_(invariant \wrapped(pl))
		_(invariant \wrapped(conf))
		_(invariant consistent_conf(pl, conf))
		_(invariant ps->size < PS_SIZE)
		_(invariant consistent == TRUE ==> \forall int j; (j >= 0 && j < conf->preflist_size) ==> ls->local_store[pl->preference_list[coord * conf->preflist_size + j]] == val)
		_(writes ls)
		_(writes ps)
		_(writes hhs)
	{
		_(assert consistent == FALSE)
		while(i < conf->preflist_size)
			_(decreases conf->preflist_size - i)
			_(invariant \wrapped(ln))
			_(invariant \wrapped(hhs))
			_(invariant \wrapped(ls))
			_(invariant \wrapped(ps))
			_(invariant \wrapped(pl))
			_(invariant \wrapped(conf))
			_(invariant consistent_conf(pl, conf))
			_(invariant ps->size < PS_SIZE)
			_(invariant ps->size <= \old(ps->size))
			_(invariant consistent == TRUE ==> \forall int j; (j >= 0 && j < conf->preflist_size) ==> ls->local_store[pl->preference_list[coord * conf->preflist_size + j]] == ls->local_store[pl->preference_list[coord * conf->preflist_size]])
			_(invariant consistent == TRUE ==> \forall int j; (j >= 0 && j < conf->preflist_size) ==> ls->local_store[pl->preference_list[coord * conf->preflist_size + j]] == val)
		{
			int index = coord * conf->preflist_size + i;
			cur_node = pl->preference_list[index];
			//_(ghost coord_times_plsize_lemma(coord, conf->preflist_size, conf->vnodes))
			if(star() && ps->size > 0) {
				rm_pending_rr(pl, ls, ps, conf);
			}

			val = merge(val, ls->local_store[cur_node]);

			if(star() && ps->size > 0) {
				rm_pending_rr(pl, ls, ps, conf);
			}

			i ++;			
		}
		consistent = harness_read_repair_aux(key, coord, ln, pl, hhs, ls, ps, conf, val, consistent, cur_node);
		if (consistent == TRUE) 
			break;	
		consistent = FALSE; // this should be redundant
	}
	_(assert \forall int j; (j >= 0 && j < conf->preflist_size) ==> ls->local_store[pl->preference_list[coord * conf->preflist_size + j]] == val)
}

