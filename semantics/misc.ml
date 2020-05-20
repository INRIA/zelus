exception Error
        
let main_node = ref (None: string option)
let set_main s = main_node := Some(s)

let set_check = ref false
              
let number_of_steps = ref 0
let set_number n = number_of_steps := n
 
