module SSet = Set.Make(String)

let l_zeluc = [
  "basics" ;
  "char" ;
  "complex" ;
  "dump" ;
  "graphics" ;
  "int32" ;
  "int64" ;
  "list" ;
  "nativeint" ;
  "node" ;
  "random" ;
  "run" ;
  "stdlib" ;
  "string" ;
  "jax" ;
  "numpy"
]

let l_probzeluc = [
  "distribution" ;
  "infer_ds_naive" ;
  "infer_ds_streaming_copy" ;
  "infer_ds_streaming" ;
  "infer_importance" ;
  "infer_pf" ;
  "probzelus"
]

let module_names_zeluc = SSet.of_list l_zeluc

let module_names_probzeluc = SSet.of_list l_probzeluc