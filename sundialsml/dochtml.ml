(***********************************************************************)
(*                                                                     *)
(*              Ocaml interface to Sundials CVODE solver               *)
(*                                                                     *)
(*           Timothy Bourke (INRIA) and Marc Pouzet (LIENS)            *)
(*                                                                     *)
(*  Copyright 2013 Institut National de Recherche en Informatique et   *)
(*  en Automatique.  All rights reserved.  This file is distributed    *)
(*  under the terms of the GNU Library General Public License, with    *)
(*  the special exception on linking described in file LICENSE.        *)
(*                                                                     *)
(***********************************************************************)

(**
 Custom tags for the ocamldoc comments:
    @cvode          link to Sundials CVODE documentation
 *)

let cvode_doc_root =
  ref "https://computation.llnl.gov/casc/sundials/documentation/cv_guide/"

class dochtml =
  object(self)
    inherit Odoc_html.html

    val rex_cvode = Str.regexp "<\\([^#>]*\\)\\(#[^)]*\\)?> \\(.*\\)"

    method html_of_cvode t =
      let s = Odoc_info.text_string_of_text t in
      if not (Str.string_match rex_cvode s 0) then
        failwith "Bad parse!"
      else
        let page = Str.matched_group 1 s
        and anchor = try
              Str.matched_group 2 s
            with Not_found -> ""
        and title = Str.matched_group 3 s
        in
        Printf.sprintf
          "<div class=\"cvode\"><small>
              See sundials: <a href=\"%s%s.html%s\">%s</a>
            </small></div>"
          !cvode_doc_root page anchor title

    initializer
      tag_functions <- ("cvode", self#html_of_cvode) :: tag_functions

  end

let option_cvode_doc_root =
  ("-cvode-doc-root", Arg.String (fun d -> cvode_doc_root := d), 
   "<dir>  specify the root url for the Sundials CVODE documentation.")

let _ =
  let dochtml = new dochtml in
  Odoc_args.add_option option_cvode_doc_root;
  Odoc_args.set_doc_generator
    (Some (dochtml :> Odoc_args.doc_generator))

