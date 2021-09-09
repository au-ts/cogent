theory WordArrayAssm
  imports
    WordArrayCorrespondence
    WordArrayMono
    WordArrayScorres
    "build/Generated_AllRefine"
begin

sublocale WordArray \<subseteq> Generated_cogent_shallow _ upd.wa_abs_repr val.wa_abs_typing_v upd.wa_abs_typing_u wa_abs_upd_val
  by (unfold_locales)

end