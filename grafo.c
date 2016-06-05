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

struct grafo {
    UINT    g_nvertices;
    UINT    g_naresta;
    int     g_tipo;
    bool	g_ponderado;
    char*	g_nome;
    lista   g_vertices;             // lista de vértices.
    lista   g_arestas;              // lista geral de todas as arestas.
};

struct vertice {
    char*	v_nome;
    int*	v_lbl;
    bool	visitado;
    lista   v_arestas;
};

struct aresta {
	bool	a_ponderado;
	int		pad;
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

void print_debug(grafo g);
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
    g->g_arestas = constroi_lista();
    for( Ag_v=agfstnode(Ag_g); Ag_v; Ag_v=agnxtnode(Ag_g, Ag_v) ) {
    	/* construct data for the actual vertex */
        v = (vertice)mymalloc(sizeof(struct vertice));
        memset(v, 0, sizeof(struct vertice));
        v->v_nome = strdup(agnameof(Ag_v));
        v->v_lbl  = (int*)mymalloc(sizeof(int) * g->g_nvertices);
		memset(v->v_lbl, 0, sizeof(int) * g->g_nvertices);
        v->v_arestas = constroi_lista();
        /* Insert vertex to the list of vertexes in the graph list. */
        if( ! insere_lista(v, g->g_vertices) ) exit(EXIT_FAILURE);
    }

    /* get all edges; neighborhood of all vertexes */
    BuildList build_list[2];
    build_list[0] = BuildListOfEdges;
    build_list[1] = BuildListOfArrows;
    for( Ag_v=agfstnode(Ag_g); Ag_v; Ag_v=agnxtnode(Ag_g, Ag_v) )
    	build_list[g->g_tipo](g, Ag_g, Ag_v, agnameof(Ag_v));
    print_debug(g);

    agclose(Ag_g);
    return g;
}

//------------------------------------------------------------------------------
// devolve uma lista de vertices com a ordem dos vértices dada por uma 
// busca em largura lexicográfica
lista busca_largura_lexicografica(grafo g) {
	no 		nv;
	vertice v;
	lista 	sequencia = constroi_lista();
	PHEAP 	heap = heap_alloc(g->g_nvertices);

	for (no nv = primeiro_no(g->g_vertices); nv; nv = proximo_no(nv)) {
		vertice v = conteudo(nv);
		v->v_lbl = (int*)malloc(sizeof(int) * (size_t)g->g_nvertices);
		for( int i = 0; i < g->g_nvertices; i++ )
			*(v->v_lbl+i) = 0;
	}

	heap_push(heap, conteudo(primeiro_no(g->g_vertices)));
	int label_atual = g->g_nvertices;
	while( (v = heap_pop(heap)) != NULL ) {
		if (v->visitado == -1)
			continue;
		v->visitado = -1; // -1 quer dizer que já foi inserido na sequencia
		insere_lista(v, sequencia);
		for (no na = primeiro_no(v->vizinhos_saida); na; na = proximo_no(na)) {
			struct aresta *a = conteudo(na);
			if (!a->visitada) {
				vertice outro = a->origem == v ? a->destino : a->origem;
				if (outro->visitado != -1) {
					int i = 0;
					while (outro->label[i])
						i++;
					outro->label[i] = label_atual;
				}
				if (!outro->visitado) { //não foi inserido na sequencia nem na heap
					pushheap(h, outro);
					outro->visitado = 1; // 1 indica que já foi inserido na heap
				}
				a->visitada = 1;
			}
		}
		heapify(h);
		label_atual--;
	}

	for (no nv = primeiro_no(g->vertices); nv; nv = proximo_no(nv)) {
		vertice vv = conteudo(nv);
		free(vv->label);
	}
	desvisita_vertices(g);
	desvisita_arestas(g);
	freeheap(h);

	return sequencia;*/
	UNUSED(g);
	return NULL;
}

//------------------------------------------------------------------------------
// devolve 1, se a lista l representa uma 
//            ordem perfeita de eliminação para o grafo g ou
//         0, caso contrário
//
// o tempo de execução é O(|V(G)|+|E(G)|)
int ordem_perfeita_eliminacao(lista l, grafo g) {
	UNUSED(l); UNUSED(g);
	return 0;
}

/*________________________________________________________________*/
grafo escreve_grafo(FILE *output, grafo g) {
	vertice v;
    aresta 	a;
    char 	rep_aresta;

    fprintf( output, "strict %sgraph \"%s\" {\n\n",
    		direcionado(g) ? "di" : "", g->g_nome
    );

    for( no n=primeiro_no(g->g_vertices); n; n=proximo_no(n) ) {
    	v = (vertice)conteudo(n);
        fprintf( output, "    \"%s\"\n", v->v_nome );
    }
    fprintf( output, "\n" );

    if( g->g_naresta ) {
    	rep_aresta = direcionado(g) ? '>' : '-';
        for( no n=primeiro_no(g->g_arestas); n; n=proximo_no(n) ) {
            a = conteudo(n);

            fprintf(output, "    \"%s\" -%c \"%s\"",
                a->a_orig->v_nome, rep_aresta, a->a_dst->v_nome
            );

            if ( a->a_ponderado )
                fprintf( output, " [peso=%ld]", a->a_peso );

            fprintf( output, "\n" );
        }
    }
    fprintf( output, "}\n" );

    return g;
}

/*________________________________________________________________*/
int cordal(grafo g) {
	UNUSED(g);
	return 0;
}

/*________________________________________________________________*/
int destroi_grafo(void *c) {
	grafo g = (grafo)c;
	int ret;
	
	free(g->g_nome);
	ret = destroi_lista(g->g_vertices, destroi_vertice);
	destroi_lista(g->g_arestas, NULL);
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
	ret = destroi_lista(v->v_arestas, destroi_aresta);
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
	Agedge_t* 	Ag_e;
	aresta 		a;
	char*		weight;
	char		str_weight[5] = "peso";
	vertice		head, tail;

	for( Ag_e=agfstedge(Ag_g, Ag_v); Ag_e; Ag_e=agnxtedge(Ag_g, Ag_e, Ag_v) ) {
		a = (aresta)mymalloc(sizeof(struct aresta));
		memset(a, 0, sizeof(struct aresta));
		weight = agget(Ag_e, str_weight);
		if( weight ) {
			a->a_peso = atol(weight);
			a->a_ponderado = TRUE;
			g->g_ponderado = TRUE;
		}
		head = busca_vertice(agnameof(agtail(Ag_e)),\
				agnameof(aghead(Ag_e)), g->g_vertices, &tail);
		check_head_tail(head_name, &head, &tail);
		a->a_orig = head;
		a->a_dst  = tail;
		if( ! insere_lista(a, head->v_arestas ) ) exit(EXIT_FAILURE);
		if( ! busca_aresta(g->g_arestas, a) )
			if( ! insere_lista(a, g->g_arestas) ) exit(EXIT_FAILURE);
	}
}

static void BuildListOfArrows(grafo g, Agraph_t* Ag_g, Agnode_t* Ag_v, const char* head_name) {
	Agedge_t* 	Ag_e;
	aresta 		a;
	char*		weight;
	char		str_weight[5] = "peso";
	vertice		head, tail;

	for( Ag_e=agfstout(Ag_g, Ag_v); Ag_e; Ag_e=agnxtout(Ag_g, Ag_e) ) {
		a = (aresta)mymalloc(sizeof(struct aresta));
		memset(a, 0, sizeof(struct aresta));
		weight = agget(Ag_e, str_weight);
		if( weight ) {
			a->a_peso = atol(weight);
			a->a_ponderado = TRUE;
			g->g_ponderado = TRUE;
		}
		head = busca_vertice(agnameof(agtail(Ag_e)),\
				agnameof(aghead(Ag_e)), g->g_vertices, &tail);
		check_head_tail(head_name, &head, &tail);
		a->a_orig = head;
		a->a_dst  = tail;
		if( ! insere_lista(a, head->v_arestas ) ) exit(EXIT_FAILURE);
		if( ! busca_aresta(g->g_arestas, a) )
			if( ! insere_lista(a, g->g_arestas) ) exit(EXIT_FAILURE);

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

/*________________________________________________________________*/
void print_debug(grafo g) {
	no 		n, n2;
	vertice v;
	aresta	a;

	dbg("Vertex...\n");
	for( n=primeiro_no(g->g_vertices); n; n=proximo_no(n) ) {
		v = conteudo(n);
		dbg("(%s, %p)\n", v->v_nome, v);
	}

	dbg("Neighbors...\n");
	for( n=primeiro_no(g->g_vertices); n; n=proximo_no(n) ) {
		v = conteudo(n);
		dbg("(%s, %p)\n", v->v_nome, v);

		n2 = primeiro_no(v->v_arestas);
		if( n2 ) {
			a = conteudo(n2);
			dbg("\t(%s, %s)", a->a_orig->v_nome, a->a_dst->v_nome);
			for( n2=proximo_no(n2); n2; n2=proximo_no(n2) ) {
				a = conteudo(n2);
				dbg(", (%s, %s)", a->a_orig->v_nome, a->a_dst->v_nome);
			}
			putchar('\n');
		}
	}

	dbg("List of edges...\n");
	n = primeiro_no(g->g_arestas);
	a = conteudo(n);
	dbg("\t(%s, %s)", a->a_orig->v_nome, a->a_dst->v_nome);
	for( n=proximo_no(n); n; n=proximo_no(n) ) {
		a = conteudo(n);
		dbg(", (%s, %s)", a->a_orig->v_nome, a->a_dst->v_nome);
	}
	putchar('\n');

 }
/*
 *##################################################################
 * Block that represents module for heap.
 *##################################################################
 */
#define DAD(k) 		( ((k) - 1) >> 1 )
#define L_CHILD(k)	( (((k) + 1) << 1) - 1 )
#define R_CHILD(k)	( ((k) + 1) << 1 );

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

	return *(x+i) > *(y+i);
}

int lbl_ge(int *x, int *y) {
	int i = 0;

	while( *(x+i) == *(y+i) ) {
		if( *(x+i) == 0 )
			return 1;
		i++;
	}

	return *(x+i) >= *(y+i);
}

void heap_push(PHEAP heap, vertice data) {
	int u, z;
	vertice tmp;

	if( heap->pos == heap->elem ) return;

	z = heap->pos;
	*(heap->v+z) = data;
	heap->pos++;

	while( z ) { /* while not root */
		u = DAD(z);
		if( lbl_ge((*(heap->v+u))->v_lbl , (*(heap->v+z))->v_lbl) ) break;

		tmp = *(heap->v + u);
		*(heap->v+u) = *(heap->v + z);
		*(heap->v+z) = tmp;
		z = u;
	}
}

vertice heap_pop(PHEAP heap) {
	int k, l, r, child;
	vertice tmp, ret;

	if( heap->pos == 0 ) return NULL;

	ret = *heap->v;
	heap->pos--;
	heap->v = (heap->v + heap->pos);

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
}

void heap_sort(PHEAP heap, int i) {
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

}

void heapify(PHEAP heap) {
	for( int i = heap->pos >> 1; i >= 0; --i )
		heap_sort(heap, i);
}
