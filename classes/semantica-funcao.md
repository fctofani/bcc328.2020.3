# Análise semântica: declaração de função

- Vamos acrescentar à linguagem fonte do projeto **declaração de função**.

- Novas **regras de produção**:

  _Dec_ → _FunDecGroup_  
    
  _FunDecGroup_ → _FunDec_  
  _FunDecGroup_ → _FunDec_ _FunDecGroup_  
    
  _FunDec_ → `function` `id` `(` _Params_ `)` `:` `id` `=` _Exp_  
    
  _Params_ →  
  _Params_ → _Param_ _ParamsRest_  
    
  _ParamsRest_ →  
  _ParamsRest_ → `,` _Param_ _ParamRest_  
    
  _Param_ → `id` `:` `id`  

- Exemplo:
  ```
  let
     function imc(peso: real, altura: real): real =
        peso / altura ^ 2
  in
     printreal(imc(69.1, 179.5))
  ```

- Exemplo: **funções mutuamente recursivas**
  ```
  let
     function par(n: int): bool =
        n = 0 || impar(n-1)

     function impar(n: int): bool =
        n > 0 && par(n-1)
  in
     printbool(impar(17))
  ```
  - Funções mutuamente recursivas devem ser declaradas em **sequência**, adjacentes uma à outra.



## Regras semânticas

- A **análise semântica** do grupo de declarações de função deve ser feita em **duas etapas**, por causa da possibilidade de recursividade mútua.

- Se fosse fazer em uma única etapa, não teria como checar a chamada de uma função antes da sua declaração.
  - No exemplo acima, a compilação de `par` daria erro, pois no momento em que o seu corpo fosse verificado a função `impar` ainda não teria sido declarada.

- **Primeira etapa**: para cada declaração de função no grupo:

  - Verificar os **parâmetros formais**:
    - checar na tabela de símbolos o nome do tipo de cada parâmetro formal,
      - obtendo a sua representação interna,
      - ou reportando erro caso não encontre
    - verificar se há parâmetro formal repetido, reportando erro em caso afirmativo
    
  - Checar na tabela de símbolos o nome do tipo do **resultado**,
    - obtendo a sua representação interna,
    - ou reportando erro caso não encontre

  - **Estender o ambiente** para incluir o nome da função e sua assinatura na tabela de símbolas de variáveis e funções
    - Assinatura:
      - lista dos tipos dos parâmetros formais
      - tipo do resultado
      
- **Segunda etapa**: para cada declaração no grupo:
    
  - Obter a **assinatura** de tipo da função no ambiente.
  
  - Verificar o **corpo da função**
    - usando um ambiente estendido para conter os parâmetros formais (como se fossem variáveis locais)
    - obtendo o tipo do corpo
    - verificar se o tipo do corpo é compatível com o tipo indicado para o resultado, reportando erro caso não o seja

- O resultado da análise semântica do grupo de declaração de funções é o ambiente estendido para incluir os nomes e respectivas assinaturas das funções.

# Análise semântica: chamada de função

- A **chamada de função** é uma expressão contendo as seguintes informações em sua árvore sintática:
  - nome da função
  - lista de argumentos (expessções)
  
- Exemplos:
  ```
  substring("idade: 19", 7, 2)
  ```

## Regras semânticas

- Pesquisar o **nome** da função na tabela de variáveis e funções do ambiente:
  - se não encontrar: reportar erro
  - se encontrar, mas não for uma função (pode ser uma variável): reportar erro
  - se encontar, e for de fato uma função:
    - a **assinatura da função** (tipos dos parâmetros formais e do resultado) é obtida da tabela
    - analisar cada **argumento**, obtendo o tipo
    - verificar se o tipo de cada argumento é compatível com o tipo do parâmetro formal correspondente
      - reportar erro em caso negativo
    - verificar a quantidade de argumentos, e reportar erro caso
      - haja menos argumentos do que parâmetros formais
      - haja mais argumentos do que parâmetros formais
    - o **tipo da expressão** é o tipo do resultado da função

# Implementando e testando

- Implemntar as regras semânticas da
  - declaração de função
  - chamada de função

- Observe que será necessário alterações nos módulos:
  - `Absyn`, para definir como as árvores sintáticas das construções será representada
  - `Absyntree`, para definir como estas árvores sintáticas são convertidas para árvores genéricas, úteis para uma visualização bacana
  - `Parse`, incluindo novos símbolos terminais e não terminais, e regras de produção para a representação das novas construções
  - `Lexer`, para definir regras léxicas para os novos símbolos terminais (tokens)
  - `Semantic`, definindo as regras semânticas aqui apresentadas.

- Testar todos as possibilidades mencionadas nas regras semânticas.

- Alguns exemplos de programa fonte para teste:
  -
  ```
  sua_funcao(2, 3)
  ```
  -
  ```
  not(false)
  ```
  -
  ```
  not("bonjour")
  ```
  -
  ```
  not()
  ```
  -
  ```
  not(true, 18, "maria")
  ```
  -
  ```
  let
     function f(a: abobrinha): real = a / 2
  in
     g(0)
  ```
  -
  ```
  let
     function g(a: real): quiabo = a / 2
  in
     g(0.75)
  ```
  -
  ```
  let
     function h(peso: real, altura: real, peso: int, nome: string): real = peso / altura ^ 2
  in
     h(70.5, 165.7, 59, "pedro")
  ```
  -
  ```
  let
     function positivo(x: int): bool = 2 * x
  in
     positivo(505)
  ```
  -
  ```
  let
     function negativo(x: int): bool = x > alfa
  in
     negativo(7)
  ```
  -
  ```
  let
     function negativo(x: int): bool = x > 0
  in
     if negativo(7) then "a" else "b"
  ```
  -
  ```
  let
     function negativo(x: int): bool = x > 0
  in
     printint(negativo(7))
  ```

- Submeter como _pull request_ no [repositório do github](https://github.com/romildo/bcc328.2020.3) até o dia 22/09 (terça-feira).
