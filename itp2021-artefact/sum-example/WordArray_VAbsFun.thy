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

lemma \<xi>_simps : 
  "\<xi>m ''wordarray_put2_0''   = val_wa_put2" 
  "\<xi>m ''wordarray_get_0''    = val_wa_get"
  "\<xi>m ''wordarray_length_0'' = val_wa_length"
  "\<xi>p ''wordarray_put2''   = val_wa_put2" 
  "\<xi>p ''wordarray_get''    = val_wa_get"
  "\<xi>p ''wordarray_length'' = val_wa_length"
  "\<xi>m1 ''wordarray_fold_no_break_0'' =  
     val_wa_foldnb \<Xi> \<xi>m (foldmap_funarg_type ''wordarray_fold_no_break_0'')"
  "\<xi>m1 ''wordarray_map_no_break_0'' = 
     val_wa_mapAccumnb \<Xi> \<xi>m 
        (foldmap_funarg_type ''wordarray_map_no_break_0'') 
        (foldmap_funret_type ''wordarray_map_no_break_0'')"
  "\<xi>m1 ''wordarray_put2_0''   = val_wa_put2" 
  "\<xi>m1 ''wordarray_get_0''    = val_wa_get"
  "\<xi>m1 ''wordarray_length_0'' = val_wa_length"
  "\<xi>p1 ''wordarray_fold_no_break'' = val_wa_foldnbp \<xi>p"
  "\<xi>p1 ''wordarray_map_no_break'' = val_wa_mapAccumnbp \<xi>p"
  "\<xi>p1 ''wordarray_put2''   = val_wa_put2" 
  "\<xi>p1 ''wordarray_get''    = val_wa_get"
  "\<xi>p1 ''wordarray_length'' = val_wa_length"
  by force+

end (* of context *)

end