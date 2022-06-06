{-# LANGUAGE BangPatterns, EmptyDataDecls, EmptyCase,
             ExistentialQuantification, ScopedTypeVariables,
             NoMonomorphismRestriction, RankNTypes, PatternSynonyms,
             OverloadedStrings #-}
module MAlonzo.Code.QfoundationZ45Zcore.QtypeZ45ZarithmeticZ45ZdependentZ45ZpairZ45Ztypes where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.QfoundationZ45Zcore.QcontractibleZ45Zmaps
import qualified MAlonzo.Code.QfoundationZ45Zcore.QcontractibleZ45Ztypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.Qequivalences
import qualified MAlonzo.Code.QfoundationZ45Zcore.QfibersZ45ZofZ45Zmaps
import qualified MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes

-- foundation-core.type-arithmetic-dependent-pair-types._.map-inv-left-unit-law-Σ-is-contr
d_map'45'inv'45'left'45'unit'45'law'45'Σ'45'is'45'contr_20 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_map'45'inv'45'left'45'unit'45'law'45'Σ'45'is'45'contr_20 ~v0 ~v1
                                                           ~v2 ~v3 ~v4 v5 v6
  = du_map'45'inv'45'left'45'unit'45'law'45'Σ'45'is'45'contr_20 v5 v6
du_map'45'inv'45'left'45'unit'45'law'45'Σ'45'is'45'contr_20 ::
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_map'45'inv'45'left'45'unit'45'law'45'Σ'45'is'45'contr_20 v0 v1
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (coe v0) (coe v1)
-- foundation-core.type-arithmetic-dependent-pair-types._.map-left-unit-law-Σ-is-contr
d_map'45'left'45'unit'45'law'45'Σ'45'is'45'contr_26 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny
d_map'45'left'45'unit'45'law'45'Σ'45'is'45'contr_26 ~v0 ~v1 ~v2 ~v3
                                                    ~v4 ~v5
  = du_map'45'left'45'unit'45'law'45'Σ'45'is'45'contr_26
du_map'45'left'45'unit'45'law'45'Σ'45'is'45'contr_26 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny
du_map'45'left'45'unit'45'law'45'Σ'45'is'45'contr_26
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.du_ind'45'Σ_50
      (let v0 = \ v0 -> v0 in coe (\ v1 -> v0))
-- foundation-core.type-arithmetic-dependent-pair-types._.issec-map-inv-left-unit-law-Σ-is-contr
d_issec'45'map'45'inv'45'left'45'unit'45'law'45'Σ'45'is'45'contr_30 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_issec'45'map'45'inv'45'left'45'unit'45'law'45'Σ'45'is'45'contr_30
  = erased
-- foundation-core.type-arithmetic-dependent-pair-types._.isretr-map-inv-left-unit-law-Σ-is-contr
d_isretr'45'map'45'inv'45'left'45'unit'45'law'45'Σ'45'is'45'contr_38 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_isretr'45'map'45'inv'45'left'45'unit'45'law'45'Σ'45'is'45'contr_38
  = erased
-- foundation-core.type-arithmetic-dependent-pair-types._.is-equiv-map-left-unit-law-Σ-is-contr
d_is'45'equiv'45'map'45'left'45'unit'45'law'45'Σ'45'is'45'contr_50 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'equiv'45'map'45'left'45'unit'45'law'45'Σ'45'is'45'contr_50 ~v0
                                                                   ~v1 ~v2 ~v3 ~v4 v5
  = du_is'45'equiv'45'map'45'left'45'unit'45'law'45'Σ'45'is'45'contr_50
      v5
du_is'45'equiv'45'map'45'left'45'unit'45'law'45'Σ'45'is'45'contr_50 ::
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'equiv'45'map'45'left'45'unit'45'law'45'Σ'45'is'45'contr_50 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_is'45'equiv'45'has'45'inverse_140
      (coe
         du_map'45'inv'45'left'45'unit'45'law'45'Σ'45'is'45'contr_20
         (coe v0))
      erased erased
-- foundation-core.type-arithmetic-dependent-pair-types._.left-unit-law-Σ-is-contr
d_left'45'unit'45'law'45'Σ'45'is'45'contr_52 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_left'45'unit'45'law'45'Σ'45'is'45'contr_52 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_left'45'unit'45'law'45'Σ'45'is'45'contr_52 v5
du_left'45'unit'45'law'45'Σ'45'is'45'contr_52 ::
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_left'45'unit'45'law'45'Σ'45'is'45'contr_52 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (coe du_map'45'left'45'unit'45'law'45'Σ'45'is'45'contr_26)
      (coe
         du_is'45'equiv'45'map'45'left'45'unit'45'law'45'Σ'45'is'45'contr_50
         (coe v0))
-- foundation-core.type-arithmetic-dependent-pair-types._.is-equiv-map-inv-left-unit-law-Σ-is-contr
d_is'45'equiv'45'map'45'inv'45'left'45'unit'45'law'45'Σ'45'is'45'contr_54 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'equiv'45'map'45'inv'45'left'45'unit'45'law'45'Σ'45'is'45'contr_54 ~v0
                                                                          ~v1 ~v2 ~v3 ~v4 ~v5
  = du_is'45'equiv'45'map'45'inv'45'left'45'unit'45'law'45'Σ'45'is'45'contr_54
du_is'45'equiv'45'map'45'inv'45'left'45'unit'45'law'45'Σ'45'is'45'contr_54 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'equiv'45'map'45'inv'45'left'45'unit'45'law'45'Σ'45'is'45'contr_54
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_is'45'equiv'45'has'45'inverse_140
      (coe du_map'45'left'45'unit'45'law'45'Σ'45'is'45'contr_26) erased
      erased
-- foundation-core.type-arithmetic-dependent-pair-types._.inv-left-unit-law-Σ-is-contr
d_inv'45'left'45'unit'45'law'45'Σ'45'is'45'contr_56 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_inv'45'left'45'unit'45'law'45'Σ'45'is'45'contr_56 ~v0 ~v1 ~v2 ~v3
                                                    ~v4 v5
  = du_inv'45'left'45'unit'45'law'45'Σ'45'is'45'contr_56 v5
du_inv'45'left'45'unit'45'law'45'Σ'45'is'45'contr_56 ::
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_inv'45'left'45'unit'45'law'45'Σ'45'is'45'contr_56 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (coe
         du_map'45'inv'45'left'45'unit'45'law'45'Σ'45'is'45'contr_20
         (coe v0))
      (coe
         du_is'45'equiv'45'map'45'inv'45'left'45'unit'45'law'45'Σ'45'is'45'contr_54)
-- foundation-core.type-arithmetic-dependent-pair-types._.is-equiv-pr1-is-contr
d_is'45'equiv'45'pr1'45'is'45'contr_72 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'equiv'45'pr1'45'is'45'contr_72 ~v0 ~v1 ~v2 ~v3 v4
  = du_is'45'equiv'45'pr1'45'is'45'contr_72 v4
du_is'45'equiv'45'pr1'45'is'45'contr_72 ::
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'equiv'45'pr1'45'is'45'contr_72 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QcontractibleZ45Zmaps.du_is'45'equiv'45'is'45'contr'45'map_60
      (coe
         (\ v1 ->
            coe
              MAlonzo.Code.QfoundationZ45Zcore.QcontractibleZ45Ztypes.du_is'45'contr'45'equiv_184
              (coe
                 MAlonzo.Code.QfoundationZ45Zcore.QfibersZ45ZofZ45Zmaps.du_equiv'45'fib'45'pr1_194
                 (coe v1))
              (coe v0 v1)))
-- foundation-core.type-arithmetic-dependent-pair-types._.equiv-pr1
d_equiv'45'pr1_80 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_equiv'45'pr1_80 ~v0 ~v1 ~v2 ~v3 v4 = du_equiv'45'pr1_80 v4
du_equiv'45'pr1_80 ::
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_equiv'45'pr1_80 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.d_pr1_26)
      (coe du_is'45'equiv'45'pr1'45'is'45'contr_72 (coe v0))
-- foundation-core.type-arithmetic-dependent-pair-types._.right-unit-law-Σ-is-contr
d_right'45'unit'45'law'45'Σ'45'is'45'contr_88 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_right'45'unit'45'law'45'Σ'45'is'45'contr_88 ~v0 ~v1 ~v2 ~v3
  = du_right'45'unit'45'law'45'Σ'45'is'45'contr_88
du_right'45'unit'45'law'45'Σ'45'is'45'contr_88 ::
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_right'45'unit'45'law'45'Σ'45'is'45'contr_88
  = coe du_equiv'45'pr1_80
-- foundation-core.type-arithmetic-dependent-pair-types._.is-contr-is-equiv-pr1
d_is'45'contr'45'is'45'equiv'45'pr1_92 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'contr'45'is'45'equiv'45'pr1_92 ~v0 ~v1 ~v2 ~v3 v4 v5
  = du_is'45'contr'45'is'45'equiv'45'pr1_92 v4 v5
du_is'45'contr'45'is'45'equiv'45'pr1_92 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'contr'45'is'45'equiv'45'pr1_92 v0 v1
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QcontractibleZ45Ztypes.du_is'45'contr'45'equiv''_216
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.QfibersZ45ZofZ45Zmaps.du_equiv'45'fib'45'pr1_194
         (coe v1))
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.QcontractibleZ45Zmaps.du_is'45'contr'45'map'45'is'45'equiv_128
         v0 v1)
-- foundation-core.type-arithmetic-dependent-pair-types._.map-assoc-Σ
d_map'45'assoc'45'Σ_118 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  (MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
   ()) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_map'45'assoc'45'Σ_118 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_map'45'assoc'45'Σ_118 v6
du_map'45'assoc'45'Σ_118 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_map'45'assoc'45'Σ_118 v0
  = case coe v0 of
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30 v1 v2
        -> case coe v1 of
             MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30 v3 v4
               -> coe
                    MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.du_triple_104
                    (coe v3) (coe v4) (coe v2)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- foundation-core.type-arithmetic-dependent-pair-types._.map-inv-assoc-Σ
d_map'45'inv'45'assoc'45'Σ_130 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  (MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
   ()) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_map'45'inv'45'assoc'45'Σ_130 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_map'45'inv'45'assoc'45'Σ_130 v6
du_map'45'inv'45'assoc'45'Σ_130 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_map'45'inv'45'assoc'45'Σ_130 v0
  = case coe v0 of
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30 v1 v2
        -> case coe v2 of
             MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30 v3 v4
               -> coe
                    MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.du_triple''_140
                    (coe v1) (coe v3) (coe v4)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- foundation-core.type-arithmetic-dependent-pair-types._.isretr-map-inv-assoc-Σ
d_isretr'45'map'45'inv'45'assoc'45'Σ_138 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  (MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
   ()) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_isretr'45'map'45'inv'45'assoc'45'Σ_138 = erased
-- foundation-core.type-arithmetic-dependent-pair-types._.issec-map-inv-assoc-Σ
d_issec'45'map'45'inv'45'assoc'45'Σ_146 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  (MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
   ()) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_issec'45'map'45'inv'45'assoc'45'Σ_146 = erased
-- foundation-core.type-arithmetic-dependent-pair-types._.is-equiv-map-assoc-Σ
d_is'45'equiv'45'map'45'assoc'45'Σ_154 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  (MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
   ()) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'equiv'45'map'45'assoc'45'Σ_154 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_is'45'equiv'45'map'45'assoc'45'Σ_154
du_is'45'equiv'45'map'45'assoc'45'Σ_154 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'equiv'45'map'45'assoc'45'Σ_154
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_is'45'equiv'45'has'45'inverse_140
      (coe du_map'45'inv'45'assoc'45'Σ_130) erased erased
-- foundation-core.type-arithmetic-dependent-pair-types._.assoc-Σ
d_assoc'45'Σ_160 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  (MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
   ()) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_assoc'45'Σ_160 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 = du_assoc'45'Σ_160
du_assoc'45'Σ_160 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_assoc'45'Σ_160
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (coe du_map'45'assoc'45'Σ_118)
      (coe du_is'45'equiv'45'map'45'assoc'45'Σ_154)
-- foundation-core.type-arithmetic-dependent-pair-types._.inv-assoc-Σ
d_inv'45'assoc'45'Σ_166 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  (MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
   ()) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_inv'45'assoc'45'Σ_166 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_inv'45'assoc'45'Σ_166
du_inv'45'assoc'45'Σ_166 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_inv'45'assoc'45'Σ_166
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (coe du_map'45'inv'45'assoc'45'Σ_130)
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_is'45'equiv'45'has'45'inverse_140
         (coe du_map'45'assoc'45'Σ_118) erased erased)
-- foundation-core.type-arithmetic-dependent-pair-types._.map-assoc-Σ'
d_map'45'assoc'45'Σ''_190 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_map'45'assoc'45'Σ''_190 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_map'45'assoc'45'Σ''_190 v6
du_map'45'assoc'45'Σ''_190 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_map'45'assoc'45'Σ''_190 v0
  = case coe v0 of
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30 v1 v2
        -> case coe v1 of
             MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30 v3 v4
               -> coe
                    MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.du_triple_104
                    (coe v3) (coe v4) (coe v2)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- foundation-core.type-arithmetic-dependent-pair-types._.map-inv-assoc-Σ'
d_map'45'inv'45'assoc'45'Σ''_202 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_map'45'inv'45'assoc'45'Σ''_202 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_map'45'inv'45'assoc'45'Σ''_202 v6
du_map'45'inv'45'assoc'45'Σ''_202 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_map'45'inv'45'assoc'45'Σ''_202 v0
  = case coe v0 of
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30 v1 v2
        -> case coe v2 of
             MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30 v3 v4
               -> coe
                    MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.du_triple''_140
                    (coe v1) (coe v3) (coe v4)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- foundation-core.type-arithmetic-dependent-pair-types._.issec-map-inv-assoc-Σ'
d_issec'45'map'45'inv'45'assoc'45'Σ''_210 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_issec'45'map'45'inv'45'assoc'45'Σ''_210 = erased
-- foundation-core.type-arithmetic-dependent-pair-types._.isretr-map-inv-assoc-Σ'
d_isretr'45'map'45'inv'45'assoc'45'Σ''_218 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_isretr'45'map'45'inv'45'assoc'45'Σ''_218 = erased
-- foundation-core.type-arithmetic-dependent-pair-types._.is-equiv-map-assoc-Σ'
d_is'45'equiv'45'map'45'assoc'45'Σ''_226 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'equiv'45'map'45'assoc'45'Σ''_226 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_is'45'equiv'45'map'45'assoc'45'Σ''_226
du_is'45'equiv'45'map'45'assoc'45'Σ''_226 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'equiv'45'map'45'assoc'45'Σ''_226
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_is'45'equiv'45'has'45'inverse_140
      (coe du_map'45'inv'45'assoc'45'Σ''_202) erased erased
-- foundation-core.type-arithmetic-dependent-pair-types._.assoc-Σ'
d_assoc'45'Σ''_232 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_assoc'45'Σ''_232 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 = du_assoc'45'Σ''_232
du_assoc'45'Σ''_232 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_assoc'45'Σ''_232
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (coe du_map'45'assoc'45'Σ''_190)
      (coe du_is'45'equiv'45'map'45'assoc'45'Σ''_226)
-- foundation-core.type-arithmetic-dependent-pair-types._.inv-assoc-Σ'
d_inv'45'assoc'45'Σ''_238 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_inv'45'assoc'45'Σ''_238 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_inv'45'assoc'45'Σ''_238
du_inv'45'assoc'45'Σ''_238 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_inv'45'assoc'45'Σ''_238
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (coe du_map'45'inv'45'assoc'45'Σ''_202)
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_is'45'equiv'45'has'45'inverse_140
         (coe du_map'45'assoc'45'Σ''_190) erased erased)
-- foundation-core.type-arithmetic-dependent-pair-types._.map-interchange-Σ-Σ
d_map'45'interchange'45'Σ'45'Σ_268 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_map'45'interchange'45'Σ'45'Σ_268 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
                                   v8
  = du_map'45'interchange'45'Σ'45'Σ_268 v8
du_map'45'interchange'45'Σ'45'Σ_268 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_map'45'interchange'45'Σ'45'Σ_268 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
         (case coe v0 of
            MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30 v1 v2
              -> case coe v1 of
                   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30 v3 v4
                     -> coe seq (coe v2) (coe v3)
                   _ -> MAlonzo.RTE.mazUnreachableError
            _ -> MAlonzo.RTE.mazUnreachableError)
         (case coe v0 of
            MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30 v1 v2
              -> coe
                   seq (coe v1)
                   (case coe v2 of
                      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30 v3 v4
                        -> coe v3
                      _ -> MAlonzo.RTE.mazUnreachableError)
            _ -> MAlonzo.RTE.mazUnreachableError))
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
         (case coe v0 of
            MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30 v1 v2
              -> case coe v1 of
                   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30 v3 v4
                     -> coe seq (coe v2) (coe v4)
                   _ -> MAlonzo.RTE.mazUnreachableError
            _ -> MAlonzo.RTE.mazUnreachableError)
         (case coe v0 of
            MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30 v1 v2
              -> coe
                   seq (coe v1)
                   (case coe v2 of
                      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30 v3 v4
                        -> coe v4
                      _ -> MAlonzo.RTE.mazUnreachableError)
            _ -> MAlonzo.RTE.mazUnreachableError))
-- foundation-core.type-arithmetic-dependent-pair-types._.map-inv-interchange-Σ-Σ
d_map'45'inv'45'interchange'45'Σ'45'Σ_308 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_map'45'inv'45'interchange'45'Σ'45'Σ_308 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
                                          ~v6 ~v7 v8
  = du_map'45'inv'45'interchange'45'Σ'45'Σ_308 v8
du_map'45'inv'45'interchange'45'Σ'45'Σ_308 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_map'45'inv'45'interchange'45'Σ'45'Σ_308 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
         (case coe v0 of
            MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30 v1 v2
              -> case coe v1 of
                   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30 v3 v4
                     -> coe seq (coe v2) (coe v3)
                   _ -> MAlonzo.RTE.mazUnreachableError
            _ -> MAlonzo.RTE.mazUnreachableError)
         (case coe v0 of
            MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30 v1 v2
              -> coe
                   seq (coe v1)
                   (case coe v2 of
                      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30 v3 v4
                        -> coe v3
                      _ -> MAlonzo.RTE.mazUnreachableError)
            _ -> MAlonzo.RTE.mazUnreachableError))
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
         (case coe v0 of
            MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30 v1 v2
              -> case coe v1 of
                   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30 v3 v4
                     -> coe seq (coe v2) (coe v4)
                   _ -> MAlonzo.RTE.mazUnreachableError
            _ -> MAlonzo.RTE.mazUnreachableError)
         (case coe v0 of
            MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30 v1 v2
              -> coe
                   seq (coe v1)
                   (case coe v2 of
                      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30 v3 v4
                        -> coe v4
                      _ -> MAlonzo.RTE.mazUnreachableError)
            _ -> MAlonzo.RTE.mazUnreachableError))
-- foundation-core.type-arithmetic-dependent-pair-types._.issec-map-inv-interchange-Σ-Σ
d_issec'45'map'45'inv'45'interchange'45'Σ'45'Σ_342 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_issec'45'map'45'inv'45'interchange'45'Σ'45'Σ_342 = erased
-- foundation-core.type-arithmetic-dependent-pair-types._.isretr-map-inv-interchange-Σ-Σ
d_isretr'45'map'45'inv'45'interchange'45'Σ'45'Σ_352 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_isretr'45'map'45'inv'45'interchange'45'Σ'45'Σ_352 = erased
-- foundation-core.type-arithmetic-dependent-pair-types._.is-equiv-map-interchange-Σ-Σ
d_is'45'equiv'45'map'45'interchange'45'Σ'45'Σ_362 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'equiv'45'map'45'interchange'45'Σ'45'Σ_362 ~v0 ~v1 ~v2 ~v3
                                                  ~v4 ~v5 ~v6 ~v7
  = du_is'45'equiv'45'map'45'interchange'45'Σ'45'Σ_362
du_is'45'equiv'45'map'45'interchange'45'Σ'45'Σ_362 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'equiv'45'map'45'interchange'45'Σ'45'Σ_362
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_is'45'equiv'45'has'45'inverse_140
      (coe du_map'45'inv'45'interchange'45'Σ'45'Σ_308) erased erased
-- foundation-core.type-arithmetic-dependent-pair-types._.interchange-Σ-Σ
d_interchange'45'Σ'45'Σ_370 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_interchange'45'Σ'45'Σ_370 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
  = du_interchange'45'Σ'45'Σ_370
du_interchange'45'Σ'45'Σ_370 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_interchange'45'Σ'45'Σ_370
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (coe du_map'45'interchange'45'Σ'45'Σ_268)
      (coe du_is'45'equiv'45'map'45'interchange'45'Σ'45'Σ_362)
-- foundation-core.type-arithmetic-dependent-pair-types._.map-left-swap-Σ
d_map'45'left'45'swap'45'Σ_394 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_map'45'left'45'swap'45'Σ_394 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_map'45'left'45'swap'45'Σ_394 v6
du_map'45'left'45'swap'45'Σ_394 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_map'45'left'45'swap'45'Σ_394 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (case coe v0 of
         MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30 v1 v2
           -> case coe v2 of
                MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30 v3 v4
                  -> coe v3
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
         (case coe v0 of
            MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30 v1 v2
              -> coe seq (coe v2) (coe v1)
            _ -> MAlonzo.RTE.mazUnreachableError)
         (case coe v0 of
            MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30 v1 v2
              -> case coe v2 of
                   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30 v3 v4
                     -> coe v4
                   _ -> MAlonzo.RTE.mazUnreachableError
            _ -> MAlonzo.RTE.mazUnreachableError))
-- foundation-core.type-arithmetic-dependent-pair-types._.map-inv-left-swap-Σ
d_map'45'inv'45'left'45'swap'45'Σ_420 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_map'45'inv'45'left'45'swap'45'Σ_420 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_map'45'inv'45'left'45'swap'45'Σ_420 v6
du_map'45'inv'45'left'45'swap'45'Σ_420 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_map'45'inv'45'left'45'swap'45'Σ_420 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (case coe v0 of
         MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30 v1 v2
           -> case coe v2 of
                MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30 v3 v4
                  -> coe v3
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
         (case coe v0 of
            MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30 v1 v2
              -> coe seq (coe v2) (coe v1)
            _ -> MAlonzo.RTE.mazUnreachableError)
         (case coe v0 of
            MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30 v1 v2
              -> case coe v2 of
                   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30 v3 v4
                     -> coe v4
                   _ -> MAlonzo.RTE.mazUnreachableError
            _ -> MAlonzo.RTE.mazUnreachableError))
-- foundation-core.type-arithmetic-dependent-pair-types._.isretr-map-inv-left-swap-Σ
d_isretr'45'map'45'inv'45'left'45'swap'45'Σ_440 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_isretr'45'map'45'inv'45'left'45'swap'45'Σ_440 = erased
-- foundation-core.type-arithmetic-dependent-pair-types._.issec-map-inv-left-swap-Σ
d_issec'45'map'45'inv'45'left'45'swap'45'Σ_448 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_issec'45'map'45'inv'45'left'45'swap'45'Σ_448 = erased
-- foundation-core.type-arithmetic-dependent-pair-types._.is-equiv-map-left-swap-Σ
d_is'45'equiv'45'map'45'left'45'swap'45'Σ_456 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'equiv'45'map'45'left'45'swap'45'Σ_456 ~v0 ~v1 ~v2 ~v3 ~v4
                                              ~v5
  = du_is'45'equiv'45'map'45'left'45'swap'45'Σ_456
du_is'45'equiv'45'map'45'left'45'swap'45'Σ_456 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'equiv'45'map'45'left'45'swap'45'Σ_456
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_is'45'equiv'45'has'45'inverse_140
      (coe du_map'45'inv'45'left'45'swap'45'Σ_420) erased erased
-- foundation-core.type-arithmetic-dependent-pair-types._.equiv-left-swap-Σ
d_equiv'45'left'45'swap'45'Σ_464 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_equiv'45'left'45'swap'45'Σ_464 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_equiv'45'left'45'swap'45'Σ_464
du_equiv'45'left'45'swap'45'Σ_464 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_equiv'45'left'45'swap'45'Σ_464
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (coe du_map'45'left'45'swap'45'Σ_394)
      (coe du_is'45'equiv'45'map'45'left'45'swap'45'Σ_456)
-- foundation-core.type-arithmetic-dependent-pair-types._.map-right-swap-Σ
d_map'45'right'45'swap'45'Σ_482 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_map'45'right'45'swap'45'Σ_482 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_map'45'right'45'swap'45'Σ_482 v6
du_map'45'right'45'swap'45'Σ_482 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_map'45'right'45'swap'45'Σ_482 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
         (case coe v0 of
            MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30 v1 v2
              -> case coe v1 of
                   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30 v3 v4
                     -> coe v3
                   _ -> MAlonzo.RTE.mazUnreachableError
            _ -> MAlonzo.RTE.mazUnreachableError)
         (case coe v0 of
            MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30 v1 v2
              -> coe seq (coe v1) (coe v2)
            _ -> MAlonzo.RTE.mazUnreachableError))
      (case coe v0 of
         MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30 v1 v2
           -> case coe v1 of
                MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30 v3 v4
                  -> coe v4
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
-- foundation-core.type-arithmetic-dependent-pair-types._.map-inv-right-swap-Σ
d_map'45'inv'45'right'45'swap'45'Σ_502 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_map'45'inv'45'right'45'swap'45'Σ_502 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_map'45'inv'45'right'45'swap'45'Σ_502 v6
du_map'45'inv'45'right'45'swap'45'Σ_502 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_map'45'inv'45'right'45'swap'45'Σ_502 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
         (case coe v0 of
            MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30 v1 v2
              -> case coe v1 of
                   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30 v3 v4
                     -> coe v3
                   _ -> MAlonzo.RTE.mazUnreachableError
            _ -> MAlonzo.RTE.mazUnreachableError)
         (case coe v0 of
            MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30 v1 v2
              -> coe seq (coe v1) (coe v2)
            _ -> MAlonzo.RTE.mazUnreachableError))
      (case coe v0 of
         MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30 v1 v2
           -> case coe v1 of
                MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30 v3 v4
                  -> coe v4
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
-- foundation-core.type-arithmetic-dependent-pair-types._.issec-map-inv-right-swap-Σ
d_issec'45'map'45'inv'45'right'45'swap'45'Σ_522 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_issec'45'map'45'inv'45'right'45'swap'45'Σ_522 = erased
-- foundation-core.type-arithmetic-dependent-pair-types._.isretr-map-inv-right-swap-Σ
d_isretr'45'map'45'inv'45'right'45'swap'45'Σ_530 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_isretr'45'map'45'inv'45'right'45'swap'45'Σ_530 = erased
-- foundation-core.type-arithmetic-dependent-pair-types._.is-equiv-map-right-swap-Σ
d_is'45'equiv'45'map'45'right'45'swap'45'Σ_538 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'equiv'45'map'45'right'45'swap'45'Σ_538 ~v0 ~v1 ~v2 ~v3 ~v4
                                               ~v5
  = du_is'45'equiv'45'map'45'right'45'swap'45'Σ_538
du_is'45'equiv'45'map'45'right'45'swap'45'Σ_538 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'equiv'45'map'45'right'45'swap'45'Σ_538
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_is'45'equiv'45'has'45'inverse_140
      (coe du_map'45'inv'45'right'45'swap'45'Σ_502) erased erased
-- foundation-core.type-arithmetic-dependent-pair-types._.equiv-right-swap-Σ
d_equiv'45'right'45'swap'45'Σ_540 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_equiv'45'right'45'swap'45'Σ_540 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_equiv'45'right'45'swap'45'Σ_540
du_equiv'45'right'45'swap'45'Σ_540 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_equiv'45'right'45'swap'45'Σ_540
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (coe du_map'45'right'45'swap'45'Σ_482)
      (coe du_is'45'equiv'45'map'45'right'45'swap'45'Σ_538)
