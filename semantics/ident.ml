type t =
      { num : int;        (* a unique index *)
        source : string;  (* the original name in the source *)
      }
      
let compare id1 id2 = compare id1.num id2.num
let name id = id.source ^ "_" ^ (string_of_int id.num)
let source id = id.source
