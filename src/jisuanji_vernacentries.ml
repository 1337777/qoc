
open Pp
open CErrors
open CAst
open Util
open Names
open Nameops
open Term
open Tacmach
open Constrintern
open Prettyp
open Printer
open Goptions
open Libnames
open Globnames
open Vernacexpr
open Decl_kinds
open Constrexpr
open Redexpr
open Lemmas
open Locality
open Attributes
open Vernacentries

let () =
  declare_bool_option
    { optdepr  = false;
      optname  = "implicit arguments";
      optkey   = ["隐含" (* "隐含" "hanxu" ; OLD : "Implicit" *) ;"键入" (* "键入" "jianru" ; OLD : "Arguments" *)];
      optread  = Impargs.is_implicit_args;
      optwrite = Impargs.make_implicit_args }
