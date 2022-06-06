{-# LANGUAGE BangPatterns, EmptyDataDecls, EmptyCase,
             ExistentialQuantification, ScopedTypeVariables,
             NoMonomorphismRestriction, RankNTypes, PatternSynonyms,
             OverloadedStrings #-}
module MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Primitive

-- foundation-core.identity-types.Id
d_Id_10 a0 a1 a2 a3 = ()
data T_Id_10 = C_refl_18
-- foundation-core.identity-types.ind-Id
d_ind'45'Id_38 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  AgdaAny ->
  (AgdaAny -> T_Id_10 -> ()) ->
  AgdaAny -> AgdaAny -> T_Id_10 -> AgdaAny
d_ind'45'Id_38 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 = du_ind'45'Id_38 v5
du_ind'45'Id_38 :: AgdaAny -> AgdaAny
du_ind'45'Id_38 v0 = coe v0
-- foundation-core.identity-types._._∙_
d__'8729'__62 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  AgdaAny -> AgdaAny -> AgdaAny -> T_Id_10 -> T_Id_10 -> T_Id_10
d__'8729'__62 = erased
-- foundation-core.identity-types._.concat
d_concat_72 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  AgdaAny -> AgdaAny -> T_Id_10 -> AgdaAny -> T_Id_10 -> T_Id_10
d_concat_72 = erased
-- foundation-core.identity-types._.concat'
d_concat''_86 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  AgdaAny -> AgdaAny -> AgdaAny -> T_Id_10 -> T_Id_10 -> T_Id_10
d_concat''_86 = erased
-- foundation-core.identity-types._.inv
d_inv_106 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () -> AgdaAny -> AgdaAny -> T_Id_10 -> T_Id_10
d_inv_106 = erased
-- foundation-core.identity-types._.assoc
d_assoc_130 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> T_Id_10 -> T_Id_10 -> T_Id_10 -> T_Id_10
d_assoc_130 = erased
-- foundation-core.identity-types._.left-unit
d_left'45'unit_142 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () -> AgdaAny -> AgdaAny -> T_Id_10 -> T_Id_10
d_left'45'unit_142 = erased
-- foundation-core.identity-types._.right-unit
d_right'45'unit_150 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () -> AgdaAny -> AgdaAny -> T_Id_10 -> T_Id_10
d_right'45'unit_150 = erased
-- foundation-core.identity-types._.left-inv
d_left'45'inv_158 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () -> AgdaAny -> AgdaAny -> T_Id_10 -> T_Id_10
d_left'45'inv_158 = erased
-- foundation-core.identity-types._.right-inv
d_right'45'inv_166 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () -> AgdaAny -> AgdaAny -> T_Id_10 -> T_Id_10
d_right'45'inv_166 = erased
-- foundation-core.identity-types._.inv-inv
d_inv'45'inv_174 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () -> AgdaAny -> AgdaAny -> T_Id_10 -> T_Id_10
d_inv'45'inv_174 = erased
-- foundation-core.identity-types._.distributive-inv-concat
d_distributive'45'inv'45'concat_186 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  AgdaAny -> AgdaAny -> T_Id_10 -> AgdaAny -> T_Id_10 -> T_Id_10
d_distributive'45'inv'45'concat_186 = erased
-- foundation-core.identity-types._.is-injective-concat
d_is'45'injective'45'concat_208 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> T_Id_10 -> T_Id_10 -> T_Id_10 -> T_Id_10 -> T_Id_10
d_is'45'injective'45'concat_208 = erased
-- foundation-core.identity-types._.is-injective-concat'
d_is'45'injective'45'concat''_224 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> T_Id_10 -> T_Id_10 -> T_Id_10 -> T_Id_10 -> T_Id_10
d_is'45'injective'45'concat''_224 = erased
-- foundation-core.identity-types.ap
d_ap_244 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> T_Id_10 -> T_Id_10
d_ap_244 = erased
-- foundation-core.identity-types.ap-id
d_ap'45'id_260 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () -> AgdaAny -> AgdaAny -> T_Id_10 -> T_Id_10
d_ap'45'id_260 = erased
-- foundation-core.identity-types.ap-comp
d_ap'45'comp_286 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> T_Id_10 -> T_Id_10
d_ap'45'comp_286 = erased
-- foundation-core.identity-types.inv-con
d_inv'45'con_308 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  AgdaAny ->
  AgdaAny ->
  T_Id_10 -> AgdaAny -> T_Id_10 -> T_Id_10 -> T_Id_10 -> T_Id_10
d_inv'45'con_308 = erased
-- foundation-core.identity-types.con-inv
d_con'45'inv_332 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  AgdaAny ->
  AgdaAny ->
  T_Id_10 -> AgdaAny -> T_Id_10 -> T_Id_10 -> T_Id_10 -> T_Id_10
d_con'45'inv_332 = erased
-- foundation-core.identity-types._.square
d_square_364 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> T_Id_10 -> T_Id_10 -> T_Id_10 -> T_Id_10 -> ()
d_square_364 = erased
-- foundation-core.identity-types._.sq-left-whisk
d_sq'45'left'45'whisk_386 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  T_Id_10 ->
  T_Id_10 ->
  T_Id_10 -> T_Id_10 -> T_Id_10 -> T_Id_10 -> T_Id_10 -> T_Id_10
d_sq'45'left'45'whisk_386 = erased
-- foundation-core.identity-types._.sq-top-whisk
d_sq'45'top'45'whisk_402 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  T_Id_10 ->
  T_Id_10 ->
  T_Id_10 -> T_Id_10 -> T_Id_10 -> T_Id_10 -> T_Id_10 -> T_Id_10
d_sq'45'top'45'whisk_402 = erased
-- foundation-core.identity-types.tr
d_tr_428 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  AgdaAny -> AgdaAny -> T_Id_10 -> AgdaAny -> AgdaAny
d_tr_428 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 = du_tr_428 v7
du_tr_428 :: AgdaAny -> AgdaAny
du_tr_428 v0 = coe v0
-- foundation-core.identity-types.path-over
d_path'45'over_448 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  AgdaAny -> AgdaAny -> T_Id_10 -> AgdaAny -> AgdaAny -> ()
d_path'45'over_448 = erased
-- foundation-core.identity-types.refl-path-over
d_refl'45'path'45'over_470 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () -> (AgdaAny -> ()) -> AgdaAny -> AgdaAny -> T_Id_10
d_refl'45'path'45'over_470 = erased
-- foundation-core.identity-types._.lift
d_lift_498 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  AgdaAny -> AgdaAny -> T_Id_10 -> AgdaAny -> T_Id_10
d_lift_498 = erased
-- foundation-core.identity-types._.tr-concat
d_tr'45'concat_522 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> T_Id_10 -> T_Id_10 -> AgdaAny -> T_Id_10
d_tr'45'concat_522 = erased
-- foundation-core.identity-types._.eq-transpose-tr
d_eq'45'transpose'45'tr_538 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  AgdaAny ->
  AgdaAny -> T_Id_10 -> AgdaAny -> AgdaAny -> T_Id_10 -> T_Id_10
d_eq'45'transpose'45'tr_538 = erased
-- foundation-core.identity-types._.eq-transpose-tr'
d_eq'45'transpose'45'tr''_552 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  AgdaAny ->
  AgdaAny -> T_Id_10 -> AgdaAny -> AgdaAny -> T_Id_10 -> T_Id_10
d_eq'45'transpose'45'tr''_552 = erased
-- foundation-core.identity-types.tr-ap
d_tr'45'ap_586 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  () ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> T_Id_10 -> AgdaAny -> T_Id_10
d_tr'45'ap_586 = erased
-- foundation-core.identity-types.Mac-Lane-pentagon
d_Mac'45'Lane'45'pentagon_630 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> T_Id_10 -> T_Id_10 -> T_Id_10 -> T_Id_10 -> T_Id_10
d_Mac'45'Lane'45'pentagon_630 = erased
-- foundation-core.identity-types.ap-binary
d_ap'45'binary_658 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> T_Id_10 -> AgdaAny -> AgdaAny -> T_Id_10 -> T_Id_10
d_ap'45'binary_658 = erased
-- foundation-core.identity-types.triangle-ap-binary
d_triangle'45'ap'45'binary_690 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> T_Id_10 -> AgdaAny -> AgdaAny -> T_Id_10 -> T_Id_10
d_triangle'45'ap'45'binary_690 = erased
-- foundation-core.identity-types.triangle-ap-binary'
d_triangle'45'ap'45'binary''_722 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> T_Id_10 -> AgdaAny -> AgdaAny -> T_Id_10 -> T_Id_10
d_triangle'45'ap'45'binary''_722 = erased
-- foundation-core.identity-types.left-unit-ap-binary
d_left'45'unit'45'ap'45'binary_748 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny -> T_Id_10 -> T_Id_10
d_left'45'unit'45'ap'45'binary_748 = erased
-- foundation-core.identity-types.right-unit-ap-binary
d_right'45'unit'45'ap'45'binary_776 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> T_Id_10 -> AgdaAny -> T_Id_10
d_right'45'unit'45'ap'45'binary_776 = erased
-- foundation-core.identity-types.ap-refl
d_ap'45'refl_792 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () -> () -> (AgdaAny -> AgdaAny) -> AgdaAny -> T_Id_10
d_ap'45'refl_792 = erased
-- foundation-core.identity-types.ap-concat
d_ap'45'concat_818 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny -> T_Id_10 -> T_Id_10 -> T_Id_10
d_ap'45'concat_818 = erased
-- foundation-core.identity-types.ap-inv
d_ap'45'inv_840 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> T_Id_10 -> T_Id_10
d_ap'45'inv_840 = erased
-- foundation-core.identity-types.apd
d_apd_862 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> T_Id_10 -> T_Id_10
d_apd_862 = erased
