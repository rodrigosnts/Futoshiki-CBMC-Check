#include <assert.h>
#include <stdbool.h>

/*
  Futoshiki 5x5 com CBMC (Model Checking)

  Funcionamento:
  - Cada célula grid[i][j] é um inteiro não determinístico (1..N).
  - Impõe-se unicidade nas linhas e colunas.
  - Desigualdades e valores fixos são aplicados dinamicamente.
  - __CPROVER_assert verifica validade das entradas.
*/

#define N 5

// Função nativa do CBMC para criar inteiros não-determinísticos.
int __CPROVER_nondet_int(void);

// Estrutura para valores fixos
typedef struct {
    int linha;
    int coluna;
    int valor;
} ValorFixo;

// Estrutura para desigualdades
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

    // VARIÁVEIS SIMBÓLICAS
    for (int i = 0; i < N; i++)
    {
        for (int j = 0; j < N; j++)
        {
            grid[i][j] = __CPROVER_nondet_int();
            __CPROVER_assume(grid[i][j] >= 1 && grid[i][j] <= N);
        }
    }

    // RESTRIÇÕES DE UNICIDADE

    // Linhas distintas
    for (int i = 0; i < N; i++)
        for (int j = 0; j < N; j++)
            for (int k = j + 1; k < N; k++)
                __CPROVER_assume(grid[i][j] != grid[i][k]);

    // Colunas distintas
    for (int j = 0; j < N; j++)
        for (int i = 0; i < N; i++)
            for (int k = i + 1; k < N; k++)
                __CPROVER_assume(grid[i][j] != grid[k][j]);

    // DESIGUALDADES
    for (int i = 0; i < sizeof(desigualdade) / sizeof(desigualdade[0]); i++)
    {
        // Validação dos índices
        __CPROVER_assert(desigualdade[i].linha_1 == desigualdade[i].linha_2, "Desigualdade em linhas diferentes");
        __CPROVER_assert(desigualdade[i].coluna_2 == desigualdade[i].coluna_1 + 1, "Colunas não adjacentes");
        __CPROVER_assert(desigualdade[i].linha_1 >= 0 && desigualdade[i].linha_1 < N, "Linha_1 fora do intervalo");
        __CPROVER_assert(desigualdade[i].linha_2 >= 0 && desigualdade[i].linha_2 < N, "Linha_2 fora do intervalo");
        __CPROVER_assert(desigualdade[i].coluna_1 >= 0 && desigualdade[i].coluna_1 < N, "Coluna_1 fora do intervalo");
        __CPROVER_assert(desigualdade[i].coluna_2 >= 0 && desigualdade[i].coluna_2 < N, "Coluna_2 fora do intervalo");

        // Aplicação da desigualdade
        __CPROVER_assume(grid[desigualdade[i].linha_1][desigualdade[i].coluna_1] >
                         grid[desigualdade[i].linha_2][desigualdade[i].coluna_2]);
    }

    // VALORES FIXOS
    for (int i = 0; i < sizeof(valores) / sizeof(valores[0]); i++)
    {
        // Validação dos índices e valor
        __CPROVER_assert(valores[i].linha >= 0 && valores[i].linha < N, "Linha fora do intervalo");
        __CPROVER_assert(valores[i].coluna >= 0 && valores[i].coluna < N, "Coluna fora do intervalo");
        __CPROVER_assert(valores[i].valor > 0 && valores[i].valor <= N, "Valor fora do intervalo");

        // Aplicação do valor fixo
        __CPROVER_assume(grid[valores[i].linha][valores[i].coluna] == valores[i].valor);
    }

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
