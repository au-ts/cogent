theory WordArray_UAbsFun
  imports WordArray_Update

begin

context WordArray begin

section "First Order"

fun \<xi>0 :: "(funtyp, abstyp, ptrtyp) uabsfuns" 
  where
  "\<xi>0 x y z = 
    (if x = ''wordarray_put2_0'' then upd_wa_put2_0 y z
     else if x = ''wordarray_get_0'' then upd_wa_get_0 y z
     else if x = ''wordarray_length_0'' then upd_wa_length_0 y z
     else False)" 

section "Second Order"

fun \<xi>1 :: "(funtyp, abstyp, ptrtyp) uabsfuns" 
  where
  "\<xi>1 x y z = 
    (if x = ''wordarray_fold_no_break_0'' then upd_wa_foldnb \<Xi> \<xi>0 (foldmap_funarg_type x) y z
     else if x = ''wordarray_map_no_break_0''
        then upd_wa_mapAccumnb \<Xi> \<xi>0 (foldmap_funarg_type x) (foldmap_funret_type x) y z 
     else \<xi>0 x y z)" 

end (* of context *)

end