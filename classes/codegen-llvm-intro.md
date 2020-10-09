# Introdução à geração de código com LLVM

- [LLVM](https://llvm.org/) (anteriormente *Low Level Virtual Machine*) é uma infraestrutura de compilador esrita em C++, desenvolvida para otimização e geração de código objeto.

- Usa uma [representação intermediária (LLVM IR)](https://llvm.org/docs/LangRef.html) que deve ser produzida pelo _front end_ do compilador.

- Implementa C, C++, e outras linguagens de programação.

# Exemplo de programa em LLVM IR

- Programa que calcula e exibe o triplo de 5

  ``` llvm
  ; ModuleID = 'triple.ll'

  declare i32 @printf(i8* nocapture readonly, ...)

  @msg = private constant [4 x i8] c"%i\0A\00"

  define i32 @triple(i32 %n) {
  entry:
    %temp = mul nsw i32 %n, 3
    ret i32 %temp
  }

  define i32 @main() {
  start:
    %result = call i32 @triple(i32 5)
    %str = getelementptr [4 x i8], [4 x i8]* @msg, i64  0, i64 0
    call i32 (i8*, ...) @printf(i8* %str, i32 %result)
    ret i32 0
  }

  ```

- Deve-se instalar:
  - clang
  - llvm
  - bindings do llvm para OCaml

- Compilando e executando:
  ```
  $ llc triple.ll

  $ clang triple.s -o triple

  $ ./triple
  15
  ```

# Gerando programas em LLVM IR

- A biblioteca LLVM permite a geração de programas na IR de forma programada.

- Tem um excelente [tutorial](https://llvm.org/docs/GettingStartedTutorials.html).

- Implementada originalmente em [C++](https://llvm.org/doxygen/index.html).

- Existem _bindings_ para outras linguagens, como [C](https://llvm.org/doxygen/group__LLVMC.html), [OCaml](https://github.com/llvm/llvm-project/tree/master/llvm/bindings/ocaml), Go e Python.

- Mais adiante veremos a geração do programa acima usando a biblioteca LLVM do OCaml.

# Alguns fundamentos

- O **contexto** em LLVM IR é uma estrutura abstrata que contém os dados globais para gerenciar a infraestrutura do LLVM em uma _thread_.
  - Várias funções da biblioteca usam o contexto.
  - Inicialmente estes dados eram globais.

- O **módulo** contém declarações de variáveis e funções.
  - Uma aplicação pode ser formada por vários módulos.
  
- **Bloco básico** é um container de instruções que são executadas sequencialmente.
  - São valores que podem ser referenciados por outras instruções tais como desvios em estruturas condicionais e de repetição.
  
- **Builder** é uma estrutura abstrata usada para construir instruções e representa uma posição em um bloco básico.

# Exemplo em OCaml

- Mesmo programa acima, gerado usando a biblioteca LLVM.
  ``` ocaml
  (* Gen_triple *)

  let context = Llvm.global_context ()

  let the_module = Llvm.create_module context "my cool triple program"

  let builder = Llvm.builder context

  let int_type = Llvm.i32_type context

  let str_type = Llvm.pointer_type (Llvm.i8_type context)

  let printf =
    Llvm.declare_function "printf" (Llvm.var_arg_function_type int_type [|str_type|]) the_module

  let triple =
    let f = Llvm.declare_function "triple" (Llvm.function_type int_type [|int_type|]) the_module in
    let block = Llvm.append_block context "entry" f in
    Llvm.position_at_end block builder;
    let n = Array.get (Llvm.params f) 0 in
    let three = Llvm.const_int int_type 3 in
    let ret = Llvm.build_mul n three "tmp" builder in
    let _ = Llvm.build_ret ret builder in
    Llvm_analysis.assert_valid_function f;
    f

  let main =
    let f = Llvm.declare_function "main" (Llvm.function_type int_type [||]) the_module in
    let block = Llvm.append_block context "start" f in
    Llvm.position_at_end block builder;
    let five = Llvm.const_int int_type 5 in
    let result = Llvm.build_call triple [|five|] "result" builder in
    let msg = Llvm.build_global_stringptr "%d\n" "" builder in
    let _ = Llvm.build_call printf [|msg; result|] "calltmp" builder in
    let ret = Llvm.const_int int_type 0 in
    let _ = Llvm.build_ret ret builder in
    Llvm_analysis.assert_valid_function f;
    f

  let _ =
    Llvm.print_module "gtriple.ll" the_module;
    print_endline "gtriple.ll has been generated"

  ```

- O arquivo `dune` deve mencionar a biblioteca `llvm`:

  ``` dune
  (executable
    (name gen_triple)
    (libraries
      llvm
      llvm.analysis))
  ```

- Compilando e executando o gerador:
  ```
  $ dune build src/gen-triple/gen_triple.exe

  $ dune exec src/gen-triple/gen_triple.exe
  gtriple.ll has been generated
  ```

- Programa gerado:
  ``` llvm
  ; ModuleID = 'my cool triple program'
  source_filename = "my cool triple program"

  @0 = private unnamed_addr constant [4 x i8] c"%d\0A\00", align 1

  declare i32 @printf(i8*, ...)

  define i32 @triple(i32 %0) {
  entry:
    %tmp = mul i32 %0, 3
    ret i32 %tmp
  }

  define i32 @main() {
  start:
    %result = call i32 @triple(i32 5)
    %calltmp = call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([4 x i8], [4 x i8]* @0, i32 0, i32 0), i32 %result)
    ret i32 0
  }
  ```

# Próximas aulas

- Vamos começar a fazer o gerador de código intermediário do compilador usando a biblioteca do LLVM.
