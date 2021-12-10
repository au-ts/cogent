theory WordArray_VAbsFun
  imports WordArray_Value

begin

context WordArray begin

section "First Order"

fun \<xi>m :: "(funtyp, vabstyp) vabsfuns" 
  where
  "\<xi>m x y z = 
    (if x = ''wordarray_put2_0'' then val_wa_put2 y z
     else if x = ''wordarray_get_0'' then val_wa_get y z
     else if x = ''wordarray_length_0'' then val_wa_length y z
     else False)" 

fun \<xi>p :: "(funtyp, vabstyp) vabsfuns" 
  where
  "\<xi>p x y z = 
    (if x = ''wordarray_put2'' then val_wa_put2 y z
     else if x = ''wordarray_get'' then val_wa_get y z
     else if x = ''wordarray_length'' then val_wa_length y z
     else False)" 

section "Second Order"

fun \<xi>m1 :: "(funtyp, vabstyp) vabsfuns" 
  where
  "\<xi>m1 x y z = 
    (if x = ''wordarray_fold_no_break_0'' then val_wa_foldnb \<Xi> \<xi>m (foldmap_funarg_type x) y z
     else if x = ''wordarray_map_no_break_0''
      then val_wa_mapAccumnb \<Xi> \<xi>m (foldmap_funarg_type x) (foldmap_funret_type x) y z
     else \<xi>m x y z)" 

fun \<xi>p1 :: "(funtyp, vabstyp) vabsfuns" 
  where
  "\<xi>p1 x y z = 
    (if x = ''wordarray_fold_no_break'' 
      then val_wa_foldnbp \<xi>p y z
     else if x = ''wordarray_map_no_break''
      then val_wa_mapAccumnbp \<xi>p y z
     else \<xi>p x y z)" 

end (* of context *)

end