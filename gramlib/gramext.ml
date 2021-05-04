(* camlp5r *)
(* gramext.ml,v *)
(* Copyright (c) INRIA 2007-2017 *)

type position =
  | Top
  | First
  | Last
  | Before of string
  | After of string
  | Level of string

type g_assoc = NonA | RightA | LeftA
