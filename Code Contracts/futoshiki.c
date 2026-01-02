#include <assert.h>
#include <stdbool.h>

#define N 5

extern int nondet_int(void);

typedef struct {
    int linha;
    int coluna;
    int valor;
} ValorFixo;

typedef struct {
    int linha_1;
    int coluna_1;
    int linha_2;
    int coluna_2;
} Desigualdade;

#define SIZE_DESIGUALDADE 3
#define SIZE_VALORES 4

Desigualdade desigualdade[] = {
    {0, 0, 0, 1},
    {0, 2, 0, 3},
    {0, 3, 0, 4}
};

ValorFixo valores[] = {
    {1, 0, 4},
    {2, 2, 4},
    {3, 4, 4},
    {1, 4, 2}
};

void solve_futoshiki(
    int grid[N][N],
    Desigualdade desigualdade[],
    int size_desigualdade,
    ValorFixo valores[],
    int size_valores
)

// CONTRATOS
// 1) Todos os valores do grid estão entre 1 e N 
__CPROVER_ensures(
  __CPROVER_forall {
    int i1;
    (0 <= i1 && i1 < N) ==> __CPROVER_forall {
      int j1;
      (0 <= j1 && j1 < N) ==> (grid[i1][j1] >= 1 && grid[i1][j1] <= N)
    }
  }
)

// 2) Linhas contêm valores distintos 
__CPROVER_ensures(
  __CPROVER_forall {
    int i2;
    (0 <= i2 && i2 < N) ==> __CPROVER_forall {
      int a2;
      (0 <= a2 && a2 < N) ==> __CPROVER_forall {
        int b2;
        (0 <= b2 && b2 < N) && a2 != b2 ==> (grid[i2][a2] != grid[i2][b2])
      }
    }
  }
)

// 3) Colunas contêm valores distintos
__CPROVER_ensures(
  __CPROVER_forall {
    int j3;
    (0 <= j3 && j3 < N) ==> __CPROVER_forall {
      int a3;
      (0 <= a3 && a3 < N) ==> __CPROVER_forall {
        int b3;
        (0 <= b3 && b3 < N) && a3 != b3 ==> (grid[a3][j3] != grid[b3][j3])
      }
    }
  }
)

// 4) Todas as desigualdades são respeitadas 
__CPROVER_ensures(
  __CPROVER_forall {
    int d4;
    (0 <= d4 && d4 < size_desigualdade) ==>
      (grid[desigualdade[d4].linha_1][desigualdade[d4].coluna_1] >
       grid[desigualdade[d4].linha_2][desigualdade[d4].coluna_2])
  }
)

// 5) Todos os valores fixos são respeitados 
__CPROVER_ensures(
  __CPROVER_forall {
    int v5;
    (0 <= v5 && v5 < size_valores) ==>
      (grid[valores[v5].linha][valores[v5].coluna] == valores[v5].valor)
  }
)


{
    for (int i = 0; i < N; i++)
        for (int j = 0; j < N; j++) {
            grid[i][j] = nondet_int();
            __CPROVER_assume(grid[i][j] >= 1 && grid[i][j] <= N);
        }

    // Unicidade por linha
    for (int i = 0; i < N; i++)
        for (int j = 0; j < N; j++)
            for (int k = j + 1; k < N; k++)
                __CPROVER_assume(grid[i][j] != grid[i][k]);

    // Unicidade por coluna
    for (int j = 0; j < N; j++)
        for (int i = 0; i < N; i++)
            for (int k = i + 1; k < N; k++)
                __CPROVER_assume(grid[i][j] != grid[k][j]);

    // Desigualdades dinâmicas (validar índices e aplicar restrição)
    for (int d = 0; d < size_desigualdade; d++) {
        __CPROVER_assert(desigualdade[d].linha_1 == desigualdade[d].linha_2, "Desigualdade em linhas diferentes");
        __CPROVER_assert(desigualdade[d].coluna_2 == desigualdade[d].coluna_1 + 1, "Colunas não adjacentes");
        __CPROVER_assert(desigualdade[d].linha_1 >= 0 && desigualdade[d].linha_1 < N, "Linha_1 fora do intervalo");
        __CPROVER_assert(desigualdade[d].linha_2 >= 0 && desigualdade[d].linha_2 < N, "Linha_2 fora do intervalo");
        __CPROVER_assert(desigualdade[d].coluna_1 >= 0 && desigualdade[d].coluna_1 < N, "Coluna_1 fora do intervalo");
        __CPROVER_assert(desigualdade[d].coluna_2 >= 0 && desigualdade[d].coluna_2 < N, "Coluna_2 fora do intervalo");

        __CPROVER_assume(
            grid[desigualdade[d].linha_1][desigualdade[d].coluna_1] >
            grid[desigualdade[d].linha_2][desigualdade[d].coluna_2]
        );
    }

    // Valores fixos
    for (int v = 0; v < size_valores; v++) {
        __CPROVER_assert(valores[v].linha >= 0 && valores[v].linha < N, "Linha fora do intervalo");
        __CPROVER_assert(valores[v].coluna >= 0 && valores[v].coluna < N, "Coluna fora do intervalo");
        __CPROVER_assert(valores[v].valor > 0 && valores[v].valor <= N, "Valor fora do intervalo");

        __CPROVER_assume(
            grid[valores[v].linha][valores[v].coluna] == valores[v].valor
        );
    }
}

int main(void)
{
    int grid[N][N];

    solve_futoshiki(
        grid,
        desigualdade,
        SIZE_DESIGUALDADE,
        valores,
        SIZE_VALORES
    );

    return 0;
}

