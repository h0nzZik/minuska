(
 (language imp)
 (semantics imp.m)
 (parser_exe "parser/_build/install/default/bin/parser")
 (parser_builder "cd parser; dune build @all")
 (static_model "klike")
 (program_info (std_module "trivial"))
)

