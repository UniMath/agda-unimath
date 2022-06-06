{-# LANGUAGE BangPatterns, EmptyDataDecls, EmptyCase,
             ExistentialQuantification, ScopedTypeVariables,
             NoMonomorphismRestriction, RankNTypes, PatternSynonyms,
             OverloadedStrings #-}
module MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Primitive

-- foundation-core.dependent-pair-types.Σ
d_Σ_12 a0 a1 a2 a3 = ()
data T_Σ_12 = C_pair_30 AgdaAny AgdaAny
-- foundation-core.dependent-pair-types.Σ.pr1
d_pr1_26 :: T_Σ_12 -> AgdaAny
d_pr1_26 v0
  = case coe v0 of
      C_pair_30 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- foundation-core.dependent-pair-types.Σ.pr2
d_pr2_28 :: T_Σ_12 -> AgdaAny
d_pr2_28 v0
  = case coe v0 of
      C_pair_30 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- foundation-core.dependent-pair-types.ind-Σ
d_ind'45'Σ_50 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  (T_Σ_12 -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> T_Σ_12 -> AgdaAny
d_ind'45'Σ_50 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 = du_ind'45'Σ_50 v6 v7
du_ind'45'Σ_50 ::
  (AgdaAny -> AgdaAny -> AgdaAny) -> T_Σ_12 -> AgdaAny
du_ind'45'Σ_50 v0 v1
  = case coe v1 of
      C_pair_30 v2 v3 -> coe v0 v2 v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- foundation-core.dependent-pair-types.ev-pair
d_ev'45'pair_76 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  (T_Σ_12 -> ()) ->
  (T_Σ_12 -> AgdaAny) -> AgdaAny -> AgdaAny -> AgdaAny
d_ev'45'pair_76 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8
  = du_ev'45'pair_76 v6 v7 v8
du_ev'45'pair_76 ::
  (T_Σ_12 -> AgdaAny) -> AgdaAny -> AgdaAny -> AgdaAny
du_ev'45'pair_76 v0 v1 v2
  = coe v0 (coe C_pair_30 (coe v1) (coe v2))
-- foundation-core.dependent-pair-types.triple
d_triple_104 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  AgdaAny -> AgdaAny -> AgdaAny -> T_Σ_12
d_triple_104 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8
  = du_triple_104 v6 v7 v8
du_triple_104 :: AgdaAny -> AgdaAny -> AgdaAny -> T_Σ_12
du_triple_104 v0 v1 v2
  = coe C_pair_30 (coe v0) (coe C_pair_30 (coe v1) (coe v2))
-- foundation-core.dependent-pair-types.triple'
d_triple''_140 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  (T_Σ_12 -> ()) -> AgdaAny -> AgdaAny -> AgdaAny -> T_Σ_12
d_triple''_140 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8
  = du_triple''_140 v6 v7 v8
du_triple''_140 :: AgdaAny -> AgdaAny -> AgdaAny -> T_Σ_12
du_triple''_140 v0 v1 v2
  = coe C_pair_30 (coe C_pair_30 (coe v0) (coe v1)) (coe v2)
-- foundation-core.dependent-pair-types._.fam-Σ
d_fam'45'Σ_176 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () -> (AgdaAny -> ()) -> (AgdaAny -> AgdaAny -> ()) -> T_Σ_12 -> ()
d_fam'45'Σ_176 = erased
