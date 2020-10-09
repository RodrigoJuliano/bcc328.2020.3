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
