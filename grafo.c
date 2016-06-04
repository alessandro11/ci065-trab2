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

struct grafo {
    UINT    g_nvertices;
    UINT    g_naresta;
    int     g_tipo;
    int     g_ponderado;
    char*	g_nome;
    lista   g_vertices;             // lista de vértices.
    lista   g_arestas;              // lista geral de todas as arestas.
};

struct vertice {
    char*	v_nome;
    USHORT*	v_lbl;
    lista   v_arestas;
};

struct aresta {
    LINT    a_pad;
    LINT	a_peso;
    vertice	a_orig;         // tail
    vertice	a_dst;          // head
};
typedef struct aresta *aresta;

void print_debug(grafo g);
vertice busca_vertice(const char* tail, const char* head,
		lista vertices, vertice* vdst);
void check_head_tail(const char* vname, vertice* head, vertice* tail);
int busca_aresta(lista l, aresta a);
int destroi_vertice(void* c);
int destroi_aresta(void* c);


/*________________________________________________________________*/
char 	*nome_grafo(grafo g)		{ return g->g_nome; }
char	*nome_vertice(vertice v)	{ return v->v_nome; }
int		direcionado(grafo g)		{ return g->g_tipo; }
int		ponderado(grafo g)			{ return g->g_ponderado; }
UINT	n_vertices(grafo g)			{ return g->g_nvertices;   }
UINT	n_arestas(grafo g)			{ return g->g_naresta; }

#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wcast-qual"
/*________________________________________________________________*/
grafo le_grafo(FILE *input) {
    Agraph_t    *Ag_g;
    Agnode_t	*Ag_v;
	Agedge_t	*Ag_e;
    grafo       g;
    vertice		v, head, tail;
    aresta		a;
    char*		peso;
    char*		vname;
    int			err;

    g = (grafo)malloc(sizeof(struct grafo));
    if( !g ) {
    	perror("Erro ao alocar memoria!");
        return NULL;
    }
	memset(g, 0, sizeof(struct grafo));

    Ag_g = agread(input, NULL);
    if ( !Ag_g ) {
    	free(g);
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
        v = (vertice)malloc(sizeof(struct vertice));
        if( !v ) goto CleanUp;
        memset(v, 0, sizeof(struct vertice));
        v->v_nome = strdup( agnameof(Ag_v) );
        v->v_lbl  = (USHORT*)malloc(sizeof(USHORT) * g->g_nvertices);
		memset(v->v_lbl, 0, sizeof(USHORT) * g->g_nvertices);
        v->v_arestas = constroi_lista();
        /* Insert vertex to the list of vertexes in the graph list. */
        if( ! insere_lista(v, g->g_vertices) ) {
        	err = errno;
        	goto CleanUp;
        }
    }

    /* get all edges; neighborhood of all vertexes */
    for( Ag_v=agfstnode(Ag_g); Ag_v; Ag_v=agnxtnode(Ag_g, Ag_v) ) {
    	vname = agnameof(Ag_v);
		for( Ag_e=agfstedge(Ag_g, Ag_v); Ag_e; Ag_e=agnxtedge(Ag_g, Ag_e, Ag_v) ) {
			a = (aresta)malloc(sizeof(struct aresta));
			if( !a ) {
				err = errno;
				goto CleanUp;
			}
			memset(a, 0, sizeof(struct aresta));
			a->a_peso = 1L;
			peso = agget(Ag_e, (char*)"peso");
			if( peso ) {
				a->a_peso = atol(peso);
				g->g_ponderado = TRUE;
			}
			head = busca_vertice(agnameof(agtail(Ag_e)), \
					agnameof(aghead(Ag_e)), g->g_vertices, &tail);
            check_head_tail(vname, &head, &tail);
            a->a_orig = head;
            a->a_dst  = tail;
			if( ! insere_lista(a, head->v_arestas ) ) {
				err = errno;
				goto CleanUp;
			}
			if( ! busca_aresta(g->g_arestas, a) ) {
				if( ! insere_lista(a, g->g_arestas)	) {
					err = errno;
					goto CleanUp;
				}
			}
		}
    }
    print_debug(g);

    agclose(Ag_g);
    return g;

CleanUp:
	if( g ) free(g);
	fprintf(stderr, "%s\n", strerror(err));
	return NULL;
}


//------------------------------------------------------------------------------
// devolve uma lista de vertices com a ordem dos vértices dada por uma 
// busca em largura lexicográfica
lista busca_largura_lexicografica(grafo g) {

	return NULL;
}

//------------------------------------------------------------------------------
// devolve 1, se a lista l representa uma 
//            ordem perfeita de eliminação para o grafo g ou
//         0, caso contrário
//
// o tempo de execução é O(|V(G)|+|E(G)|)
int ordem_perfeita_eliminacao(lista l, grafo g) {
	return 0;
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

/*________________________________________________________________*/
#define dbg(fmt, ...) \
	do { \
		fprintf(stderr, fmt, ## __VA_ARGS__); \
	} while(0)
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
		a = conteudo(n2);
		dbg("\t(%s, %s)", a->a_orig->v_nome, a->a_dst->v_nome);
		for( n2=proximo_no(n2); n2; n2=proximo_no(n2) ) {
			a = conteudo(n2);
			dbg(", (%s, %s)", a->a_orig->v_nome, a->a_dst->v_nome);
		}
		putchar('\n');
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

//            if ( a->a_ponderado )
//                fprintf( output, " [peso=%ld]", a->a_peso );

            fprintf( output, "\n" );
        }
    }

    fprintf( output, "}\n" );
    return g;
}

/*________________________________________________________________*/
int cordal(grafo g) {
	return 0;
}

/*________________________________________________________________*/
int destroi_grafo(void *c) {
	grafo g = (grafo)c;
	int ret;
	
	free(g->g_nome);
	ret = destroi_lista(g->g_vertices, destroi_vertice);
	ret &= destroi_lista(g->g_arestas, NULL);
	free(c);

	return ret;
}

/*________________________________________________________________*/
int destroi_vertice(void* c) {
	vertice v = (vertice)c;

	free(v->v_nome);
	free(v->v_lbl);
	
	return destroi_lista(v->v_arestas, destroi_aresta);
}

int destroi_aresta(void* c) {
	free(c);
	return 1;
}
#pragma GCC diagnostic pop
