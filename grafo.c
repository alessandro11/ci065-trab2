/*
 * =====================================================================================
 *
 *       Filename:  grafo.c
 *
 *    Description:  
 *
 *        Version:  1.0
 *        Created:  05/21/2016 12:04:32 PM
 *       Revision:  none
 *       Compiler:  gcc
 *
 *         Author:  Alessandro Elias (BCC), ae11@c3sl.ufpr.br
 *            GRR:  20110589
 *
 * =====================================================================================
 */

#include <stdio.h>
#include <stdlib.h>
#define __USE_XOPEN_EXTENDED
#include <string.h>
#include <errno.h>
#include <graphviz/cgraph.h>
#include "grafo.h"
#include "lista.h"

typedef unsigned int UINT;
typedef long int LINT;
typedef unsigned short USHORT;
typedef int bool;

#ifndef TRUE
#define TRUE		1
#endif

#ifndef FALSE
#define FALSE		0
#endif

typedef enum __state {
	eNotSet = 0,
	eVisited,
	eInserted
}eState;

struct grafo {
    UINT    g_nvertices;
    UINT    g_naresta;
    int     g_tipo;
    bool	g_ponderado;
    char*	g_nome;
    lista   g_vertices;             // lista de vértices.
};

struct vertice {
    char*	v_nome;
    int*	v_lbl;
    eState	visitado;
    int		v_index;
    lista	v_neighborhood_in;
    lista	v_neighborhood_out;
};

struct aresta {
	bool	a_ponderado;
	eState	visitada;
    LINT	a_peso;
    vertice	a_orig;         // tail
    vertice	a_dst;          // head
};
typedef struct aresta *aresta;

typedef struct __heap {
	int 		elem;
	int 		pos;
	vertice*	v;
}HEAP;
typedef HEAP* PHEAP;

/*
 * MACROS
 */
#define UNUSED(x)			(void)(x)
#define dbg(fmt, ...) \
	do { \
		fprintf(stderr, fmt, ## __VA_ARGS__); \
	} while(0)
#define FPF_ERR(fmt, ...)	(fprintf(stderr, (fmt), ## __VA_ARGS__))

vertice busca_vertice(const char* tail, const char* head,
		lista vertices, vertice* vdst);
void check_head_tail(const char* vname, vertice* head, vertice* tail);
int busca_aresta(lista l, aresta a);
int destroi_vertice(void* c);
int destroi_aresta(void* c);
void* mymalloc(size_t size);
static void BuildListOfEdges(grafo g, Agraph_t* Ag_g, Agnode_t* Ag_v, const char* head_name);
static void BuildListOfArrows(grafo g, Agraph_t* Ag_g, Agnode_t* Ag_v, const char* head_name);
typedef void (*BuildList)(grafo, Agraph_t*, Agnode_t*, const char*);
void heapify(PHEAP heap);
void heap_sort(PHEAP heap, int i);
vertice heap_pop(PHEAP heap);
void heap_push(PHEAP heap, vertice data);
int lbl_ge(int *x, int *y);
int lbl_g(int *x, int *y);
void heap_free(PHEAP heap);
PHEAP heap_alloc(int elem);
void set_none_vertexes(grafo g);
vertice primeiro_vizinho_a_direita(lista l);
void set_none_arestas(grafo g);


/*________________________________________________________________*/
char 	*nome_grafo(grafo g)		{ return g->g_nome; }
char	*nome_vertice(vertice v)	{ return v->v_nome; }
int		direcionado(grafo g)		{ return g->g_tipo; }
int		ponderado(grafo g)			{ return g->g_ponderado; }
UINT	n_vertices(grafo g)			{ return g->g_nvertices;   }
UINT	n_arestas(grafo g)			{ return g->g_naresta; }

/*________________________________________________________________*/
grafo le_grafo(FILE *input) {
    Agraph_t*	Ag_g;
    Agnode_t*	Ag_v;
    grafo       g;
    vertice		v;

    g = (grafo)mymalloc(sizeof(struct grafo));
	memset(g, 0, sizeof(struct grafo));

    Ag_g = agread(input, NULL);
    if ( !Ag_g ) {
    	free(g);
    	FPF_ERR("Could not read graph!\n");
        return NULL;
    }

    g->g_nome = strdup(agnameof(Ag_g));
    g->g_tipo = agisdirected(Ag_g);
    g->g_nvertices= (UINT)agnnodes(Ag_g);
    g->g_naresta = (UINT)agnedges(Ag_g);
    g->g_vertices = constroi_lista();
    for( Ag_v=agfstnode(Ag_g); Ag_v; Ag_v=agnxtnode(Ag_g, Ag_v) ) {
    	/* construct data for the actual vertex */
        v = (vertice)mymalloc(sizeof(struct vertice));
        memset(v, 0, sizeof(struct vertice));
        v->v_nome = strdup(agnameof(Ag_v));
        v->v_lbl  = (int*)mymalloc(sizeof(int) * g->g_nvertices);
		memset(v->v_lbl, 0, sizeof(int) * g->g_nvertices);
        v->v_neighborhood_in = constroi_lista();
        v->v_neighborhood_out = constroi_lista();
        /* Insert vertex to the list of vertexes in the graph list. */
        if( !insere_lista(v, g->g_vertices) ) exit(EXIT_FAILURE);
    }

    /* get all edges; neighborhood of all vertexes */
    BuildList build_list[2];
    build_list[0] = BuildListOfEdges;
    build_list[1] = BuildListOfArrows;
    for( Ag_v=agfstnode(Ag_g); Ag_v; Ag_v=agnxtnode(Ag_g, Ag_v) )
    	build_list[g->g_tipo](g, Ag_g, Ag_v, agnameof(Ag_v));

    agclose(Ag_g);
    return g;
}

void print_a(lista l) {
	no n;
	struct aresta* a;

	n=primeiro_no(l);
	if( n ) {
		a = conteudo(n);
		printf("\t\to=%s  d=%s\n", a->a_orig->v_nome, a->a_dst->v_nome);
		for( n=proximo_no(n); n; n=proximo_no(n) ) {
			a = conteudo(n);
			printf("\t\to=%s  d=%s\n", a->a_orig->v_nome, a->a_dst->v_nome);
		}
	}
	fflush(stdout);
}

void lprint_vertexes(lista l) {
	no n;
	struct vertice* v;

	for( n=primeiro_no(l); n; n=proximo_no(n) ) {
		v = conteudo(n);
		printf("%s\n", v->v_nome);
		printf("\tVizinhos in:\n");
		print_a(v->v_neighborhood_in);
		printf("\tVizinhos out:\n");
		print_a(v->v_neighborhood_out);
	}
	fflush(stdout);
}

void print_vertexes(grafo g) {
	no n;
	struct vertice* v;
	lista l = g->g_vertices;

	for( n=primeiro_no(l); n; n=proximo_no(n) ) {
		v = conteudo(n);
		printf("%s\n", v->v_nome);
		printf("\tVizinhos in:\n");
		print_a(v->v_neighborhood_in);
		printf("\tVizinhos out:\n");
		print_a(v->v_neighborhood_out);
	}
	fflush(stdout);
}

//------------------------------------------------------------------------------
// devolve uma lista de vertices com a ordem dos vértices dada por uma 
// busca em largura lexicográfica
lista busca_largura_lexicografica(grafo g) {
	no 		na;
	vertice v, aux;
	aresta	a;
	int 	current_lbl, i;
	lista 	perf_seq;
	PHEAP 	heap;

	perf_seq = constroi_lista();
	heap = heap_alloc((int)g->g_nvertices);
	heap_push(heap, conteudo(primeiro_no(g->g_vertices)));
	current_lbl = (int)g->g_nvertices;
	while( (v = heap_pop(heap)) != NULL ) {
		if( v->visitado == eInserted ) continue;
		v->visitado = eInserted; // -1 quer dizer que já foi inserido na perf_seq
		insere_lista(v, perf_seq);
		for( na = primeiro_no(v->v_neighborhood_out); na; na = proximo_no(na) ) {
			a = conteudo(na);
			if( !a->visitada ) {
				aux = a->a_orig == v ? a->a_dst : a->a_orig;
				if( aux->visitado != eInserted ) {
					i = 0;
					while( *(aux->v_lbl+i++) );
					*(aux->v_lbl+i) = current_lbl;
				}
				if( !aux->visitado ) { //não foi inserido na perf_seq nem na heap
					heap_push(heap, aux);
					aux->visitado = eVisited; // 1 indica que já foi inserido na heap
				}
				a->visitada = eVisited;
			}
		}
		heapify(heap);
		--current_lbl;
	}

	set_none_vertexes(g);
	set_none_arestas(g);
	heap_free(heap);

	return perf_seq;

	/*
	// assume que g é conexo??
	#define pushheap heap_push
	#define freeheap heap_free
	#define popheap	 heap_pop

	lista perf_seq = constroi_lista();
	// insere no começo sempre, então perf_seq final já será invertida
	PHEAP 	h = heap_alloc((int)g->g_nvertices);

//	for (no nv = primeiro_no(g->g_vertices); nv; nv = proximo_no(nv)) {
//		vertice v = conteudo(nv);
//		v->v_lbl = malloc(sizeof(int) * (size_t)g->g_nvertices);
//		for (int i = 0; i < (int)g->g_nvertices; i++) {
//			v->v_lbl[i] = 0;
//		}
//	}

	pushheap(h, conteudo(primeiro_no(g->g_vertices)));
	vertice v;
	int label_atual = (int)g->g_nvertices;
	while ((v = popheap(h)) != NULL) {
		if (v->visitado == -1)
			continue;
		v->visitado = -1; // -1 quer dizer que já foi inserido na perf_seq
		insere_lista(v, perf_seq);
		for (no na = primeiro_no(v->v_neighborhood_out); na; na = proximo_no(na)) {
			struct aresta *a = conteudo(na);
			if (!a->visitada) {
				vertice aux = a->a_orig == v ? a->a_dst : a->a_orig;
				if (aux->visitado != -1) {
					int i = 0;
					while (aux->v_lbl[i])
						i++;
					aux->v_lbl[i] = label_atual;
				}
				if (!aux->visitado) { //não foi inserido na perf_seq nem na heap
					pushheap(h, aux);
					aux->visitado = 1; // 1 indica que já foi inserido na heap
				}
				a->visitada = 1;
			}
		}
		heapify(h);
		label_atual--;
	}

//	for (no nv = primeiro_no(g->g_vertices); nv; nv = proximo_no(nv)) {
//		vertice vv = conteudo(nv);
//		free(vv->v_lbl);
//	}
//	desvisita_vertices(g);
//	desvisita_arestas(g);
	set_none_vertexes(g);
	set_none_arestas(g);

	freeheap(h);

	return perf_seq;
	#undef pushheap
	#undef freeheap
	#undef popheap
	*/
}

void set_none_arestas(grafo g) {
	for (no nv = primeiro_no(g->g_vertices); nv; nv = proximo_no(nv)) {
		vertice v = conteudo(nv);
		for (no na = primeiro_no(v->v_neighborhood_out); na; na = proximo_no(na))
		((aresta)conteudo(na))->visitada = eNotSet;
	}
}

void set_none_vertexes(grafo g) {
	for (no nv = primeiro_no(g->g_vertices); nv; nv = proximo_no(nv))
		((vertice)conteudo(nv))->visitado = eNotSet;
}

//------------------------------------------------------------------------------
// devolve 1, se a lista l representa uma 
//            ordem perfeita de eliminação para o grafo g ou
//         0, caso contrário
//
// o tempo de execução é O(|V(G)|+|E(G)|)
int ordem_perfeita_eliminacao(lista l, grafo g) {
	lista* 	viz_dir, l2;
	UINT 	i, count;
	no		nv, ne, n2, n3;
	aresta	e;
	vertice	v, v2, outro, tmp;

	viz_dir = (lista*)mymalloc(sizeof(lista) * (size_t) g->g_nvertices);
	for( i = 0; i < g->g_nvertices; i++ )
		*(viz_dir+i) = constroi_lista();

	count = 0;
	for( nv=primeiro_no(l); nv; nv=proximo_no(nv) ) {
		v = (vertice)conteudo(nv);
		v->visitado = eVisited;
		v->v_index = (int)count;
		for( ne=primeiro_no(v->v_neighborhood_out); ne; ne=proximo_no(ne) ) {
			e = (aresta)conteudo(ne);
			outro = e->a_orig == v ? e->a_dst : e->a_orig;
			if( outro->visitado ) continue;
			// insere na lista somente os vizinhos que estão à direita na sequencia
			// insere_lista(outro, viz_dir_outro[count]);
			insere_lista(outro, *(viz_dir+count));
		}
		++count;
	}
	set_none_vertexes(g);

	for( nv = primeiro_no(l); nv; nv = proximo_no(nv) ) {
		v = conteudo(nv);
		v2 = primeiro_vizinho_a_direita(*(viz_dir+v->v_index));
		if( !v2 ) continue;

		l2 = *(viz_dir+v2->v_index);
		for( n2 = primeiro_no(viz_dir[v->v_index]); n2; n2 = proximo_no(n2) ) {
			tmp = conteudo(n2);
			// tmp será todos os vizinhos à direita de v tirando o primeiro (v2)
			if( tmp == v2 ) continue;
			for( n3=primeiro_no(l2); n3; n3=proximo_no(n3) ) {
				if( tmp == conteudo(n3) ) break;
			}
			if( !n3 ) {
				// n3 == NULL quer dizer que esse vizinho à direita de v
				// não é vizinho à direita de v2
				for( i = 0; i < g->g_nvertices; ++i ) {
					destroi_lista(*(viz_dir+i), NULL);
				}
				free(viz_dir);
				return 0;
			}
		}
	}

	for( i = 0; i < g->g_nvertices; ++i ) {
		destroi_lista(*(viz_dir+i), NULL);
	}
	free(viz_dir);

	return 1;


	/*
	lista *viz_dir = malloc(sizeof(lista) * (size_t) g->g_nvertices);

	for (int i = 0; i < g->g_nvertices; i++)
		viz_dir[i] = constroi_lista();

	int count = 0;
	for( no nv = primeiro_no(l); nv; nv = proximo_no(nv) ) {
		vertice v = conteudo(nv);
		v->visitado = eVisited;
		v->v_index = count;
		for(no na = primeiro_no(v->v_neighborhood_out); na; na = proximo_no(na) ) {
			struct aresta *a = conteudo(na);
			vertice outro = a->a_orig == v ? a->a_dst : a->a_orig;
			if( outro->visitado )
				continue;
			// insere na lista somente os vizinhos que estão à direita na sequencia
			// insere_lista(outro, viz_dir_aux[count]);
			insere_lista(outro, viz_dir[count]);
		}
		count++;
	}
	set_none_vertexes(g);

	for( no nv = primeiro_no(l); nv; nv = proximo_no(nv) ) {
		vertice v = conteudo(nv);
		vertice v2 = primeiro_vizinho_a_direita(viz_dir[v->v_index]);
		if( !v2 )
			continue;

		lista l2 = viz_dir[v2->v_index];
		for( no n2 = primeiro_no(viz_dir[v->v_index]); n2; n2 = proximo_no(n2) ) {
			vertice tmp = conteudo(n2);
			// tmp será todos os vizinhos à direita de v tirando o primeiro (v2)
			if( tmp == v2 )
				continue;
			no n3;
			for( n3 = primeiro_no(l2); n3; n3 = proximo_no(n3) ) {
				if( tmp == conteudo(n3) )
					break;
			}
			if( !n3 ) {
				// n3 == NULL quer dizer que esse vizinho à direita de v
				// não é vizinho à direita de v2
				for (int i = 0; i < g->g_nvertices; i++) {
					destroi_lista(viz_dir[i], NULL);
				}
				free(viz_dir);
				return 0;
			}
		}
	}

	for (int i = 0; i < g->g_nvertices; i++) {
		destroi_lista(viz_dir[i], NULL);
	}
	free(viz_dir);

	return 1;
	*/
}

/*________________________________________________________________*/
grafo escreve_grafo(FILE *output, grafo g) {
	vertice v;
    aresta 	e;
    char 	ch;
    no		n, ne;

    if( !g ) return NULL;
    fprintf( output, "strict %sgraph \"%s\" {\n\n",
    		direcionado(g) ? "di" : "", g->g_nome
    );

    for( n=primeiro_no(g->g_vertices); n; n=proximo_no(n) )
        fprintf(output, "    \"%s\"\n", ((vertice)conteudo(n))->v_nome);
    fprintf( output, "\n" );

	ch = direcionado(g) ? '>' : '-';
	for( n=primeiro_no(g->g_vertices); n; n=proximo_no(n) ) {
		v = (vertice)conteudo(n);
		for( ne=primeiro_no(v->v_neighborhood_out); ne; ne=proximo_no(ne) ) {
			e = (aresta)conteudo(ne);
			if( e->visitada == eVisited ) continue;
			e->visitada = eVisited;
			fprintf(output, "    \"%s\" -%c \"%s\"",
				e->a_orig->v_nome, ch, e->a_dst->v_nome
			);

			if ( g->g_ponderado )
				fprintf( output, " [peso=%ld]", e->a_peso );
			fprintf( output, "\n" );
		}
	}
    fprintf( output, "}\n" );

    set_none_arestas(g);
    return g;
}

/*________________________________________________________________*/
int cordal(grafo g) {
	lista l;
	int r;

	l = busca_largura_lexicografica(g);
	r = ordem_perfeita_eliminacao(l, g);
	destroi_lista(l, NULL);

	return r;
}

/*________________________________________________________________*/
int destroi_grafo(void *c) {
	grafo g = (grafo)c;
	int ret;
	
	free(g->g_nome);
	ret = destroi_lista(g->g_vertices, destroi_vertice);
	free(c);

	return ret;
}

/*****
 * Functions helpers.
 *
 ******************************************************************/
int destroi_vertice(void* c) {
	int ret;
	vertice v = (vertice)c;

	free(v->v_nome);
	free(v->v_lbl);
	ret = destroi_lista(v->v_neighborhood_in, destroi_aresta) && \
		  destroi_lista(v->v_neighborhood_out, destroi_aresta);
	free(c);

	return ret;
}

int destroi_aresta(void* c) {
	free(c);
	return 1;
}

/*________________________________________________________________*/
int busca_aresta(lista l, aresta a) {
	no n;
	aresta p;
	int found = FALSE;

	for( n=primeiro_no(l); n && !found; n=proximo_no(n) ) {
		p = (aresta)conteudo(n);
		found = ( p->a_orig == a->a_dst &&\
				  p->a_dst  == a->a_orig );
	}

	return found;
}

/*________________________________________________________________*/
void check_head_tail(const char* vname, vertice* head, vertice* tail) {
    vertice tmp;

    if( strcmp(vname, (*head)->v_nome) != 0 ) {
        if( strcmp(vname, (*tail)->v_nome) == 0 ) {
            /* swap */
            tmp = *head;
            *head = *tail;
            *tail = tmp;
        }
    }
}

void* mymalloc(size_t size) {
	void* p;

	if( !(p = malloc(size)) ) {
		perror("Could not allocate memory!");
        exit(EXIT_FAILURE);
	}

	return p;
}

static void BuildListOfEdges(grafo g, Agraph_t* Ag_g, Agnode_t* Ag_v, const char* head_name) {
	UNUSED(head_name);
	Agedge_t* 	Ag_e;
	aresta 		a;
	char*		weight;
	char		str_weight[5] = "peso";
	vertice		head, tail;

	for( Ag_e=agfstedge(Ag_g, Ag_v); Ag_e; Ag_e=agnxtedge(Ag_g, Ag_e, Ag_v) ) {
		if( agtail(Ag_e) == Ag_v ) {
			a = (aresta)mymalloc(sizeof(struct aresta));
			memset(a, 0, sizeof(struct aresta));
			weight = agget(Ag_e, str_weight);
			if( weight ) {
				a->a_peso = atol(weight);
				a->a_ponderado = TRUE;
				g->g_ponderado = TRUE;
			}
			tail = busca_vertice(agnameof(agtail(Ag_e)),\
					agnameof(aghead(Ag_e)), g->g_vertices, &head);
			a->a_orig = tail;
			a->a_dst  = head;
			if( !insere_lista(a, head->v_neighborhood_out ) ) exit(EXIT_FAILURE);
			if( !insere_lista(a, tail->v_neighborhood_out ) ) exit(EXIT_FAILURE);
		}
	}
}

static void BuildListOfArrows(grafo g, Agraph_t* Ag_g, Agnode_t* Ag_v, const char* head_name) {
	Agedge_t* 	Ag_e;
	aresta 		a;
	char*		weight;
	char		str_weight[5] = "peso";
	vertice		head, tail;

	for( Ag_e=agfstout(Ag_g, Ag_v); Ag_e; Ag_e=agnxtout(Ag_g, Ag_e) ) {
		if( agtail(Ag_e) == Ag_v ) {
			a = (aresta)mymalloc(sizeof(struct aresta));
			memset(a, 0, sizeof(struct aresta));
			weight = agget(Ag_e, str_weight);
			if( weight ) {
				a->a_peso = atol(weight);
				a->a_ponderado = TRUE;
				g->g_ponderado = TRUE;
			}
			tail = busca_vertice(agnameof(agtail(Ag_e)),\
					agnameof(aghead(Ag_e)), g->g_vertices, &head);
			check_head_tail(head_name, &head, &tail);
			a->a_orig = head;
			a->a_dst  = tail;
			if( !insere_lista(a, tail->v_neighborhood_in ) ) exit(EXIT_FAILURE);
			if( !insere_lista(a, head->v_neighborhood_out ) ) exit(EXIT_FAILURE);
		}
	}
}

/******
 * Descrição:
 *  Busca um vértice de acordo com o nome.
 *
 * Param:
 * a_nome - constant string com o nome do vértice.
 *    v   - ponteiro para o primeiro elemento de veŕtices.
 *
 * Retorno:
 *  vértice se encontrado
 *  NULL caso contrário.
 *
 * OBS: ver readme para lógica criada para a alocação dos vértices.
******************************************************************************/
vertice busca_vertice(const char* tail, const char* head,
		lista vertices, vertice* vdst) {

    int many = 0;
    vertice r_tail = NULL;
    vertice tmp = NULL;
    *vdst = NULL;

    for( no n=primeiro_no(vertices); n && many < 2; n=proximo_no(n) ) {
    	tmp = (vertice)conteudo(n);
        if( strcmp(tail, tmp->v_nome) == 0 )
        	r_tail = tmp;
        if( strcmp(head, tmp->v_nome) == 0 )
        	*vdst = tmp;
    }

    return r_tail;
}

vertice primeiro_vizinho_a_direita(lista l) {
	no nv = primeiro_no(l);
	if( !nv ) return NULL;

	vertice vertice_menor_index = conteudo(nv);

	for (nv = proximo_no(nv); nv; nv = proximo_no(nv)) {
		vertice v = conteudo(nv);
		if (v->v_index < vertice_menor_index->v_index)
			vertice_menor_index = v;
	}

	return vertice_menor_index;
}

/*
 *##################################################################
 * Block that represents module for heap operations.
 *##################################################################
 */
#define DAD(k) 		( ((k) - 1) >> 1 )
#define L_CHILD(k)	( (((k) + 1) << 1) - 1 )
#define R_CHILD(k)	( ((k) + 1) << 1 );
/*
static int DAD(int x) {
    return (x-1) / 2;
}
static int L_CHILD(int x) {
    return ((x+1) * 2) - 1;
}
static int R_CHILD(int x) {
    return (x+1) * 2;
}
*/
PHEAP heap_alloc(int elem) {
	PHEAP heap = (PHEAP)malloc(sizeof(HEAP));
	if( !heap ) exit(EXIT_FAILURE);
	heap->v = (vertice*)malloc(sizeof(struct vertice) * (size_t)elem);
	if( !heap->v ) exit(EXIT_FAILURE);
	heap->elem = elem;
	heap->pos = 0;

	return heap;

}

void heap_free(PHEAP heap) {
	free(heap->v);
	free(heap);
}

int lbl_g(int *x, int *y) {
	int i = 0;

	while( *(x+i) == *(y+i) ) {
		if( *(x+i) == 0 )
			return 0;
		i++;
	}

	return( *(x+i) > *(y+i) );

	/*
    //retorna 1 se a > b
    int i = 0;
    while (x[i] == y[i]) {
        if (x[i] == 0)
            return 0;
        i++;
    }
    return x[i] > y[i];
	*/
}

int lbl_ge(int *x, int *y) {
	int i = 0;

	while( *(x+i) == *(y+i) ) {
		if( *(x+i) == 0 )
			return 1;
		i++;
	}

	return *(x+i) >= *(y+i);
	/*
    //retorna 1 se a >= b
    int i = 0;
    while (x[i] == y[i]) {
        if (x[i] == 0)
            return 1;
        i++;
    }
    return x[i] >= y[i];
	*/
}

void heap_push(PHEAP heap, vertice data) {
	int u, z;
	vertice tmp;

	if( heap->pos == heap->elem ) return;

	z = heap->pos;
	*(heap->v+z) = data;
	heap->pos++;

	while( z ) {
		u = DAD(z);
		if( lbl_ge((*(heap->v+u))->v_lbl , (*(heap->v+z))->v_lbl) ) break;

		tmp = *(heap->v + u);
		*(heap->v+u) = *(heap->v + z);
		*(heap->v+z) = tmp;
		z = u;
	}

	/*
    if (heap->pos == heap->elem)
        return;
    // heap cheia

    int z = heap->pos;
    heap->v[z] = data;
    heap->pos++;

    while (z) { //while not root
        int u = DAD(z);
        if (lbl_ge(heap->v[u]->v_lbl, heap->v[z]->v_lbl))
            break;
        //sobe o elemento na árvore
        vertice tmp = heap->v[u];
        heap->v[u] = heap->v[z];
        heap->v[z] = tmp;
        z = u;
    }
	*/
}

vertice heap_pop(PHEAP heap) {
	int k, l, r, child;
	vertice tmp, ret;

	if( heap->pos == 0 ) return NULL;

	ret = *heap->v;
	heap->pos--;
	*heap->v = *(heap->v + heap->pos);

	k = 0;
	while( (l = L_CHILD(r)) < heap->pos ) {
		r = R_CHILD(k);
		if( r < heap->pos && lbl_g((*(heap->v+l))->v_lbl, (*(heap->v+r))->v_lbl) )
			child = r;
		else child = l;

		if( lbl_g((*(heap->v+k))->v_lbl, (*(heap->v+child))->v_lbl) ) {
			tmp = *(heap->v + child);
			*(heap->v+child) = *(heap->v + k);
			*(heap->v+k) = tmp;
			k = child;
		} else break;
	}

	return ret;

	/*
    if (heap->pos == 0) {
        return NULL;
    }

    vertice retorno = heap->v[0];

    heap->pos--;
    heap->v[0] = heap->v[heap->pos]; // coloca o último como raiz

    int r = 0;
    int e;
    while ((e = L_CHILD(r)) < heap->pos) {
        int d = R_CHILD(r);
        int filho;
        if (d < heap->pos && lbl_g(heap->v[e]->v_lbl, heap->v[d]->v_lbl)) {
            filho = d;
        } else {
            filho = e;
        }
        if (lbl_g(heap->v[r]->v_lbl, heap->v[filho]->v_lbl)) {
            vertice tmp = heap->v[filho];
            heap->v[filho] = heap->v[r];
            heap->v[r] = tmp;
            r = filho;
        } else {
            break;
        }
    }

    return retorno;
	*/
}

void heap_sort(PHEAP heap, int i) {
    int l, r, maior;
    l = L_CHILD(i);
    r = R_CHILD(i);
    if ((l < heap->pos) && lbl_g(heap->v[l]->v_lbl, heap->v[i]->v_lbl)) {
        maior = l;
    } else {
        maior = i;
    }
    if ((r < heap->pos) && lbl_g(heap->v[r]->v_lbl, heap->v[i]->v_lbl)) {
        maior = r;
    }
    if (maior != i) {
        vertice tmp = heap->v[maior];
        heap->v[maior] = heap->v[i];
        heap->v[i] = tmp;
        heap_sort(heap, maior);
    }

	/*
	int l, r, g;
	vertice tmp;

	l = L_CHILD(i);
	r = R_CHILD(i);
	if( (l < heap->pos) && lbl_g((*(heap->v+l))->v_lbl, (*(heap->v+i))->v_lbl) )
		g = l;
	else
		g = i;

	if( (r < heap->pos) && lbl_g((*(heap->v+r))->v_lbl, (*(heap->v+i))->v_lbl) )
		g = r;
	if( g != i ) {
		tmp = *(heap->v+g);
		*(heap->v+g) = *(heap->v+i);
		*(heap->v+i) = tmp;
		heap_sort(heap, g);
	}
	*/
}

void heapify(PHEAP heap) {
	for( int i = heap->pos >> 1; i >= 0; --i )
		heap_sort(heap, i);
	/*
    for (int i = heap->pos/2; i >=0; i--) {
        heap_sort(heap, i);
    }
    */
}

