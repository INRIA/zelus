(** Inference with delayed sampling *)

module DS_hl = Infer_ds_hl.Make(Infer_ds_ll_gc)

include DS_hl

