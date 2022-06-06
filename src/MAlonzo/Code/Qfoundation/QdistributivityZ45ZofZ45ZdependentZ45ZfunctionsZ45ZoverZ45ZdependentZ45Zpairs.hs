{-# LANGUAGE BangPatterns, EmptyDataDecls, EmptyCase,
             ExistentialQuantification, ScopedTypeVariables,
             NoMonomorphismRestriction, RankNTypes, PatternSynonyms,
             OverloadedStrings #-}
module MAlonzo.Code.Qfoundation.QdistributivityZ45ZofZ45ZdependentZ45ZfunctionsZ45ZoverZ45ZdependentZ45Zpairs where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.Qequivalences
import qualified MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes
import qualified MAlonzo.Code.Qfoundation.QstructureZ45ZidentityZ45Zprinciple

-- foundation.distributivity-of-dependent-functions-over-dependent-pairs.Π-total-fam
d_Π'45'total'45'fam_18 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () -> (AgdaAny -> ()) -> (AgdaAny -> AgdaAny -> ()) -> ()
d_Π'45'total'45'fam_18 = erased
-- foundation.distributivity-of-dependent-functions-over-dependent-pairs.universally-structured-Π
d_universally'45'structured'45'Π_42 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () -> (AgdaAny -> ()) -> (AgdaAny -> AgdaAny -> ()) -> ()
d_universally'45'structured'45'Π_42 = erased
-- foundation.distributivity-of-dependent-functions-over-dependent-pairs._.htpy-universally-structured-Π
d_htpy'45'universally'45'structured'45'Π_78 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  ()
d_htpy'45'universally'45'structured'45'Π_78 = erased
-- foundation.distributivity-of-dependent-functions-over-dependent-pairs._.extensionality-universally-structured-Π
d_extensionality'45'universally'45'structured'45'Π_92 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_extensionality'45'universally'45'structured'45'Π_92 ~v0 ~v1 ~v2
                                                      ~v3 ~v4 ~v5 v6
  = du_extensionality'45'universally'45'structured'45'Π_92 v6
du_extensionality'45'universally'45'structured'45'Π_92 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_extensionality'45'universally'45'structured'45'Π_92 v0
  = case coe v0 of
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30 v1 v2
        -> coe
             MAlonzo.Code.Qfoundation.QstructureZ45ZidentityZ45Zprinciple.du_extensionality'45'Σ_138
             (coe v1) (coe v2) erased erased
      _ -> MAlonzo.RTE.mazUnreachableError
-- foundation.distributivity-of-dependent-functions-over-dependent-pairs._.eq-htpy-universally-structured-Π
d_eq'45'htpy'45'universally'45'structured'45'Π_114 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_eq'45'htpy'45'universally'45'structured'45'Π_114 = erased
-- foundation.distributivity-of-dependent-functions-over-dependent-pairs.map-distributive-Π-Σ
d_map'45'distributive'45'Π'45'Σ_134 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_map'45'distributive'45'Π'45'Σ_134 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_map'45'distributive'45'Π'45'Σ_134 v6
du_map'45'distributive'45'Π'45'Σ_134 ::
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_map'45'distributive'45'Π'45'Σ_134 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (coe
         (\ v1 ->
            MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.d_pr1_26
              (coe v0 v1)))
      (coe
         (\ v1 ->
            MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.d_pr2_28
              (coe v0 v1)))
-- foundation.distributivity-of-dependent-functions-over-dependent-pairs.map-inv-distributive-Π-Σ
d_map'45'inv'45'distributive'45'Π'45'Σ_158 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_map'45'inv'45'distributive'45'Π'45'Σ_158 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
                                           v6 v7
  = du_map'45'inv'45'distributive'45'Π'45'Σ_158 v6 v7
du_map'45'inv'45'distributive'45'Π'45'Σ_158 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_map'45'inv'45'distributive'45'Π'45'Σ_158 v0 v1
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.d_pr1_26
         v0 v1)
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.d_pr2_28
         v0 v1)
-- foundation.distributivity-of-dependent-functions-over-dependent-pairs.issec-map-inv-distributive-Π-Σ
d_issec'45'map'45'inv'45'distributive'45'Π'45'Σ_182 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_issec'45'map'45'inv'45'distributive'45'Π'45'Σ_182 = erased
-- foundation.distributivity-of-dependent-functions-over-dependent-pairs.isretr-map-inv-distributive-Π-Σ
d_isretr'45'map'45'inv'45'distributive'45'Π'45'Σ_206 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_isretr'45'map'45'inv'45'distributive'45'Π'45'Σ_206 = erased
-- foundation.distributivity-of-dependent-functions-over-dependent-pairs.is-equiv-map-distributive-Π-Σ
d_is'45'equiv'45'map'45'distributive'45'Π'45'Σ_226 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'equiv'45'map'45'distributive'45'Π'45'Σ_226 ~v0 ~v1 ~v2 ~v3
                                                   ~v4 ~v5
  = du_is'45'equiv'45'map'45'distributive'45'Π'45'Σ_226
du_is'45'equiv'45'map'45'distributive'45'Π'45'Σ_226 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'equiv'45'map'45'distributive'45'Π'45'Σ_226
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_is'45'equiv'45'has'45'inverse_140
      (coe du_map'45'inv'45'distributive'45'Π'45'Σ_158) erased erased
-- foundation.distributivity-of-dependent-functions-over-dependent-pairs.distributive-Π-Σ
d_distributive'45'Π'45'Σ_248 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_distributive'45'Π'45'Σ_248 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_distributive'45'Π'45'Σ_248
du_distributive'45'Π'45'Σ_248 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_distributive'45'Π'45'Σ_248
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (coe du_map'45'distributive'45'Π'45'Σ_134)
      (coe du_is'45'equiv'45'map'45'distributive'45'Π'45'Σ_226)
-- foundation.distributivity-of-dependent-functions-over-dependent-pairs.is-equiv-map-inv-distributive-Π-Σ
d_is'45'equiv'45'map'45'inv'45'distributive'45'Π'45'Σ_264 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'equiv'45'map'45'inv'45'distributive'45'Π'45'Σ_264 ~v0 ~v1
                                                          ~v2 ~v3 ~v4 ~v5
  = du_is'45'equiv'45'map'45'inv'45'distributive'45'Π'45'Σ_264
du_is'45'equiv'45'map'45'inv'45'distributive'45'Π'45'Σ_264 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'equiv'45'map'45'inv'45'distributive'45'Π'45'Σ_264
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_is'45'equiv'45'has'45'inverse_140
      (coe du_map'45'distributive'45'Π'45'Σ_134) erased erased
-- foundation.distributivity-of-dependent-functions-over-dependent-pairs.inv-distributive-Π-Σ
d_inv'45'distributive'45'Π'45'Σ_286 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_inv'45'distributive'45'Π'45'Σ_286 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_inv'45'distributive'45'Π'45'Σ_286
du_inv'45'distributive'45'Π'45'Σ_286 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_inv'45'distributive'45'Π'45'Σ_286
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (coe du_map'45'inv'45'distributive'45'Π'45'Σ_158)
      (coe du_is'45'equiv'45'map'45'inv'45'distributive'45'Π'45'Σ_264)
-- foundation.distributivity-of-dependent-functions-over-dependent-pairs.Eq-Π-total-fam
d_Eq'45'Π'45'total'45'fam_308 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  ()
d_Eq'45'Π'45'total'45'fam_308 = erased
-- foundation.distributivity-of-dependent-functions-over-dependent-pairs.extensionality-Π-total-fam
d_extensionality'45'Π'45'total'45'fam_342 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_extensionality'45'Π'45'total'45'fam_342 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
                                          v6 v7
  = du_extensionality'45'Π'45'total'45'fam_342 v6 v7
du_extensionality'45'Π'45'total'45'fam_342 ::
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_extensionality'45'Π'45'total'45'fam_342 v0 v1
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du__'8728'e__386
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du__'8728'e__386
         (coe du_inv'45'distributive'45'Π'45'Σ_286)
         (coe
            du_extensionality'45'universally'45'structured'45'Π_92
            (coe du_map'45'distributive'45'Π'45'Σ_134 (coe v0))
            (coe du_map'45'distributive'45'Π'45'Σ_134 (coe v1))))
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_equiv'45'ap_912)
-- foundation.distributivity-of-dependent-functions-over-dependent-pairs.eq-Eq-Π-total-fam
d_eq'45'Eq'45'Π'45'total'45'fam_370 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_eq'45'Eq'45'Π'45'total'45'fam_370 = erased
-- foundation.distributivity-of-dependent-functions-over-dependent-pairs.mapping-into-Σ
d_mapping'45'into'45'Σ_394 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  (AgdaAny -> ()) ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_mapping'45'into'45'Σ_394 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_mapping'45'into'45'Σ_394
du_mapping'45'into'45'Σ_394 ::
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_mapping'45'into'45'Σ_394
  = coe du_map'45'distributive'45'Π'45'Σ_134
-- foundation.distributivity-of-dependent-functions-over-dependent-pairs.is-equiv-mapping-into-Σ
d_is'45'equiv'45'mapping'45'into'45'Σ_412 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'equiv'45'mapping'45'into'45'Σ_412 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_is'45'equiv'45'mapping'45'into'45'Σ_412
du_is'45'equiv'45'mapping'45'into'45'Σ_412 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'equiv'45'mapping'45'into'45'Σ_412
  = coe du_is'45'equiv'45'map'45'distributive'45'Π'45'Σ_226
