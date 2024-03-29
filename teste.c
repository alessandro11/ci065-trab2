#include <stdio.h>
#include "grafo.h"

//------------------------------------------------------------------------------

int main(void) {

  grafo g = le_grafo(stdin);

  if ( !g )

    return 1;

//  print_vertexes(g);
//  return ! destroi_grafo(g);

//  lista l = busca_largura_lexicografica(g);
//  lprint_vertexes(l);
//  return ! destroi_grafo(g);

  printf("nome: %s\n", nome_grafo(g));
  int d = direcionado(g);
  printf("%sdirecionado\n", d ? "" : "não ");
  printf("%sponderado\n", ponderado(g) ? "" : "não ");
  unsigned n = n_vertices(g);
  printf("%d vértices\n", n);
  printf("%d arestas\n", n_arestas(g));
  escreve_grafo(stdout, g);
  printf("\n%s %s é cordal\n", nome_grafo(g), cordal(g) ? "" : "não ");


  return ! destroi_grafo(g);
}
