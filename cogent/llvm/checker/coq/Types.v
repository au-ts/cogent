From Coq Require Import ZArith List.
From Vellvm Require Import LLVMAst.
From Checker Require Import Cogent.

Open Scope Z_scope.

Definition convert_num_type (t : num_type) : typ :=
  TYPE_I match t with
  | U8 => 8
  | U16 => 16
  | U32 => 32
  | U64 => 64
  end.

Variant FieldType : Set :=
| BoxField (t : typ)
| UnboxField (t : typ)
| Invalid.

Definition field_type (t : typ) (f : field) : FieldType :=
  match t with
  | TYPE_Struct flds => 
      match (nth_error flds f) with 
      | Some x => UnboxField x
      | None => Invalid
      end
  | TYPE_Pointer (TYPE_Struct flds) =>
      match (nth_error flds f) with
      | Some x => BoxField x
      | None => Invalid
      end
  | _ => Invalid
  end.

Definition deref_type (t : typ) : typ := match t with TYPE_Pointer t' | t' => t' end.

Definition return_type (t : typ) : typ := match t with TYPE_Function t' _ | t' => t' end.
