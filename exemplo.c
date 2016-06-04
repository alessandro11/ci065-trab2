#include <stdio.h>
#include <stdlib.h>
#include <graphviz/cgraph.h>
#include "lista.h"

//------------------------------------------------------------------------------
static lista lista_arestas;

static int direcionado,
  n_vertices,
  n_arestas;

//------------------------------------------------------------------------------
static int busca_aresta(Agedge_t *a){

  for ( no n=primeiro_no(lista_arestas); n; n=proximo_no(n)) {
    
    Agedge_t *aresta = conteudo(n);

    if ( ageqedge(a, aresta) )
      
      return 1;
  }

  return 0;
}
//------------------------------------------------------------------------------
static void guarda_arestas(Agraph_t *g, Agnode_t *v) {

  for (Agedge_t *a=agfstedge(g,v); a; a=agnxtedge(g,a,v))

    if ( ! busca_aresta(a) )

  	  insere_lista(a, lista_arestas);
}
//------------------------------------------------------------------------------
static void guarda_arcos(Agraph_t *g, Agnode_t *v) {

  for (Agedge_t *a=agfstout(g,v); a; a=agnxtout(g,a))

    if ( ! busca_aresta(a) )

      insere_lista(a, lista_arestas);
}
//------------------------------------------------------------------------------
static void mostra_arestas(void) {

  if ( !n_arestas )
    return;
  
  char rep_aresta = direcionado ? '>' : '-';
  
  for ( no n=primeiro_no(lista_arestas); n; n=proximo_no(n)) {
  
    Agedge_t *a= conteudo(n);
    char *peso = agget(a, (char *)"peso");
    
    printf("    \"%s\" -%c \"%s\"",
           agnameof(agtail(a)),
           rep_aresta,
           agnameof(aghead(a))
           );

    if ( peso && *peso )
      printf(" [peso=%s]", peso);

    printf("\n");
  }
}
//------------------------------------------------------------------------------
static void mostra_vertices(Agraph_t *g) {

  if ( !n_vertices )
    return;

  for (Agnode_t *v=agfstnode(g); v; v=agnxtnode(g,v)) {

    printf("    \"%s\"\n", agnameof(v));
    
    if ( direcionado )
      guarda_arcos(g, v);
    else
      guarda_arestas(g, v);
  }
}
//------------------------------------------------------------------------------
static Agraph_t *mostra_grafo(Agraph_t *g) {

  if ( ! g )
    return NULL;

  direcionado = agisdirected(g);

  n_vertices = agnnodes(g);

  n_arestas = agnedges(g);
  
  lista_arestas = constroi_lista();

  printf("strict %sgraph \"%s\" {\n\n",
         agisdirected(g) ? "di" : "",
         agnameof(g)
         );

  mostra_vertices(g);

  printf("\n");

  mostra_arestas();

  printf("}\n");

  destroi_lista(lista_arestas, NULL);

  return g;
}
//------------------------------------------------------------------------------
int main(void) {

  Agraph_t *g = agread(stdin, NULL);

  if ( !g )
    return 1;

  agclose(mostra_grafo(g));

  return agerrors();
}
