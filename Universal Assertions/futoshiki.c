#include <assert.h>
#include <stdbool.h>

#define N 5

//int nondet_int(void);
//extern int nondet_int(void);
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

int main(void)
{
    int grid[N][N];

    Desigualdade desigualdade[] = {
        {0, 0, 0, 1},  // grid[0][0] > grid[0][1]
        {0, 2, 0, 3},  // grid[0][2] > grid[0][3]
        {0, 3, 0, 4}   // grid[0][3] > grid[0][4]
    };

    ValorFixo valores[] = {
        {1, 0, 4},  // grid[1][0] = 4
        {2, 2, 4},  // grid[2][2] = 4
        {3, 4, 4},  // grid[3][4] = 4
        {1, 4, 2}   // grid[1][4] = 2
    };


    // Variáveis simbólicas + restrição de domínio
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
    for (int d = 0; d < (int)(sizeof(desigualdade) / sizeof(desigualdade[0])); d++) {
        __CPROVER_assert(desigualdade[d].linha_1 == desigualdade[d].linha_2, "Desigualdade em linhas diferentes");
        __CPROVER_assert(desigualdade[d].coluna_2 == desigualdade[d].coluna_1 + 1, "Colunas não adjacentes");
        __CPROVER_assert(desigualdade[d].linha_1 >= 0 && desigualdade[d].linha_1 < N, "Linha_1 fora do intervalo");
        __CPROVER_assert(desigualdade[d].linha_2 >= 0 && desigualdade[d].linha_2 < N, "Linha_2 fora do intervalo");
        __CPROVER_assert(desigualdade[d].coluna_1 >= 0 && desigualdade[d].coluna_1 < N, "Coluna_1 fora do intervalo");
        __CPROVER_assert(desigualdade[d].coluna_2 >= 0 && desigualdade[d].coluna_2 < N, "Coluna_2 fora do intervalo");

        __CPROVER_assume(grid[desigualdade[d].linha_1][desigualdade[d].coluna_1] >
                         grid[desigualdade[d].linha_2][desigualdade[d].coluna_2]);
    }

    // Valores fixos dinâmicos (validar e aplicar)
    for (int v = 0; v < (int)(sizeof(valores) / sizeof(valores[0])); v++) {
        __CPROVER_assert(valores[v].linha >= 0 && valores[v].linha < N, "Linha fora do intervalo");
        __CPROVER_assert(valores[v].coluna >= 0 && valores[v].coluna < N, "Coluna fora do intervalo");
        __CPROVER_assert(valores[v].valor > 0 && valores[v].valor <= N, "Valor fora do intervalo");

        __CPROVER_assume(grid[valores[v].linha][valores[v].coluna] == valores[v].valor);
    }

    // Provas universais (asserts)
    __CPROVER_assert(
        __CPROVER_forall {
            int i;
            (0 <= i && i < N) ==> (__CPROVER_forall {
                int j;
                (0 <= j && j < N) ==> (grid[i][j] >= 1 && grid[i][j] <= N)
            })
        },
        "Todos os valores estao entre 1 e N"
    );

    __CPROVER_assert(
        __CPROVER_forall {
            int i;
            (0 <= i && i < N) ==> (__CPROVER_forall {
                int a;
                (0 <= a && a < N) ==> (__CPROVER_forall {
                    int b;
                    (0 <= b && b < N) && a != b ==> (grid[i][a] != grid[i][b])
                })
            })
        },
        "Linhas contem valores distintos"
    );

    __CPROVER_assert(
        __CPROVER_forall {
            int j;
            (0 <= j && j < N) ==> (__CPROVER_forall {
                int a;
                (0 <= a && a < N) ==> (__CPROVER_forall {
                    int b;
                    (0 <= b && b < N) && a != b ==> (grid[a][j] != grid[b][j])
                })
            })
        },
        "Colunas contem valores distintos"
    );

    __CPROVER_assert(
        __CPROVER_forall {
            int d;
            (0 <= d && d < (int)(sizeof(desigualdade)/sizeof(desigualdade[0]))) ==>
                (grid[desigualdade[d].linha_1][desigualdade[d].coluna_1] >
                 grid[desigualdade[d].linha_2][desigualdade[d].coluna_2])
        },
        "Todas as desigualdades são respeitadas"
    );

    __CPROVER_assert(
        __CPROVER_forall {
            int v;
            (0 <= v && v < (int)(sizeof(valores)/sizeof(valores[0]))) ==>
                (grid[valores[v].linha][valores[v].coluna] == valores[v].valor)
        },
        "Todos os valores fixos são respeitados"
    );

    return 0;
}

/*
    NOTAS:

    __CPROVER_assume(condição):
    Restringe o espaço de busca do CBMC, assumindo que a condição é verdadeira.
    Se for falsa, o caminho de execução é ignorado (não gera erro).

    __CPROVER_assert(condição, "mensagem"):
    Verifica se a condição é verdadeira.
    Se for falsa, o CBMC reporta uma violação/erro com a mensagem associada.

    assume → "considerar apenas casos em que isto é verdade".
    assert → "falhar se isto não for verdade".
*/

/*
  RODAR COM: cbmc futoshiki.c
*/

// mudanças proximas aula: vamos passar a usar contratos em vez de asserts. 
