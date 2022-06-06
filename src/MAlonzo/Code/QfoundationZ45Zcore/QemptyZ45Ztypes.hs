{-# LANGUAGE BangPatterns, EmptyDataDecls, EmptyCase,
             ExistentialQuantification, ScopedTypeVariables,
             NoMonomorphismRestriction, RankNTypes, PatternSynonyms,
             OverloadedStrings #-}
module MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.Qequivalences
import qualified MAlonzo.Code.QfoundationZ45Zcore.Qfunctions
import qualified MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.QtruncationZ45Zlevels
import qualified MAlonzo.Code.Qfoundation.Qpropositions

-- foundation-core.empty-types.empty
d_empty_4 = ()
data T_empty_4
-- foundation-core.empty-types.ind-empty
d_ind'45'empty_12 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  (T_empty_4 -> ()) -> T_empty_4 -> AgdaAny
d_ind'45'empty_12 ~v0 ~v1 ~v2 = du_ind'45'empty_12
du_ind'45'empty_12 :: AgdaAny
du_ind'45'empty_12 = MAlonzo.RTE.mazUnreachableError
-- foundation-core.empty-types.ex-falso
d_ex'45'falso_18 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () -> T_empty_4 -> AgdaAny
d_ex'45'falso_18 ~v0 ~v1 = du_ex'45'falso_18
du_ex'45'falso_18 :: T_empty_4 -> AgdaAny
du_ex'45'falso_18 v0 = coe du_ind'45'empty_12
-- foundation-core.empty-types.is-empty
d_is'45'empty_22 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 -> () -> ()
d_is'45'empty_22 = erased
-- foundation-core.empty-types.is-nonempty
d_is'45'nonempty_28 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 -> () -> ()
d_is'45'nonempty_28 = erased
-- foundation-core.empty-types._.is-emb-ex-falso
d_is'45'emb'45'ex'45'falso_40 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  T_empty_4 ->
  T_empty_4 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'emb'45'ex'45'falso_40 ~v0 ~v1 ~v2
  = du_is'45'emb'45'ex'45'falso_40
du_is'45'emb'45'ex'45'falso_40 ::
  T_empty_4 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'emb'45'ex'45'falso_40 = MAlonzo.RTE.mazUnreachableError
-- foundation-core.empty-types._.ex-falso-emb
d_ex'45'falso'45'emb_42 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_ex'45'falso'45'emb_42 ~v0 ~v1 = du_ex'45'falso'45'emb_42
du_ex'45'falso'45'emb_42 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_ex'45'falso'45'emb_42
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (coe du_ex'45'falso_18)
      (\ v0 -> coe du_is'45'emb'45'ex'45'falso_40)
-- foundation-core.empty-types.is-equiv-is-empty
d_is'45'equiv'45'is'45'empty_54 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> T_empty_4) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'equiv'45'is'45'empty_54 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_is'45'equiv'45'is'45'empty_54 v5
du_is'45'equiv'45'is'45'empty_54 ::
  (AgdaAny -> T_empty_4) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'equiv'45'is'45'empty_54 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_is'45'equiv'45'has'45'inverse_140
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.Qfunctions.du__'8728'__36
         (coe (\ v1 -> coe du_ex'45'falso_18)) (coe v0))
      erased erased
-- foundation-core.empty-types.is-equiv-is-empty'
d_is'45'equiv'45'is'45'empty''_70 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> T_empty_4) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'equiv'45'is'45'empty''_70 ~v0 ~v1 ~v2
  = du_is'45'equiv'45'is'45'empty''_70
du_is'45'equiv'45'is'45'empty''_70 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'equiv'45'is'45'empty''_70
  = coe du_is'45'equiv'45'is'45'empty_54 erased
-- foundation-core.empty-types.equiv-is-empty
d_equiv'45'is'45'empty_82 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  (AgdaAny -> T_empty_4) ->
  (AgdaAny -> T_empty_4) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_equiv'45'is'45'empty_82 ~v0 ~v1 ~v2 ~v3 v4 v5
  = du_equiv'45'is'45'empty_82 v4 v5
du_equiv'45'is'45'empty_82 ::
  (AgdaAny -> T_empty_4) ->
  (AgdaAny -> T_empty_4) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_equiv'45'is'45'empty_82 v0 v1
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du__'8728'e__386
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_inv'45'equiv_250
         (coe
            MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
            (coe v1) (coe du_is'45'equiv'45'is'45'empty_54 erased)))
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
         (coe v0) (coe du_is'45'equiv'45'is'45'empty_54 erased))
-- foundation-core.empty-types.is-prop-empty
d_is'45'prop'45'empty_88 ::
  T_empty_4 ->
  T_empty_4 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'prop'45'empty_88 ~v0 = du_is'45'prop'45'empty_88
du_is'45'prop'45'empty_88 ::
  T_empty_4 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'prop'45'empty_88 = MAlonzo.RTE.mazUnreachableError
-- foundation-core.empty-types.empty-Prop
d_empty'45'Prop_90 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_empty'45'Prop_90
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      erased (\ v0 -> coe du_is'45'prop'45'empty_88)
-- foundation-core.empty-types.is-set-empty
d_is'45'set'45'empty_92 ::
  T_empty_4 ->
  T_empty_4 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'set'45'empty_92 ~v0 = du_is'45'set'45'empty_92
du_is'45'set'45'empty_92 ::
  T_empty_4 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'set'45'empty_92 = MAlonzo.RTE.mazUnreachableError
-- foundation-core.empty-types.empty-Set
d_empty'45'Set_94 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_empty'45'Set_94
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      erased (\ v0 -> coe du_is'45'set'45'empty_92)
-- foundation-core.empty-types.is-trunc-empty
d_is'45'trunc'45'empty_98 ::
  MAlonzo.Code.QfoundationZ45Zcore.QtruncationZ45Zlevels.T_𝕋_4 ->
  T_empty_4 -> T_empty_4 -> AgdaAny
d_is'45'trunc'45'empty_98 ~v0 ~v1 = du_is'45'trunc'45'empty_98
du_is'45'trunc'45'empty_98 :: T_empty_4 -> AgdaAny
du_is'45'trunc'45'empty_98 = MAlonzo.RTE.mazUnreachableError
-- foundation-core.empty-types.empty-Truncated-Type
d_empty'45'Truncated'45'Type_104 ::
  MAlonzo.Code.QfoundationZ45Zcore.QtruncationZ45Zlevels.T_𝕋_4 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_empty'45'Truncated'45'Type_104 ~v0
  = du_empty'45'Truncated'45'Type_104
du_empty'45'Truncated'45'Type_104 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_empty'45'Truncated'45'Type_104
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      erased (\ v0 -> coe du_is'45'trunc'45'empty_98)
-- foundation-core.empty-types.is-trunc-is-empty
d_is'45'trunc'45'is'45'empty_116 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QtruncationZ45Zlevels.T_𝕋_4 ->
  () -> (AgdaAny -> T_empty_4) -> AgdaAny -> AgdaAny -> AgdaAny
d_is'45'trunc'45'is'45'empty_116 v0 v1 ~v2 ~v3
  = du_is'45'trunc'45'is'45'empty_116 v0 v1
du_is'45'trunc'45'is'45'empty_116 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QtruncationZ45Zlevels.T_𝕋_4 ->
  AgdaAny -> AgdaAny -> AgdaAny
du_is'45'trunc'45'is'45'empty_116 v0 v1
  = coe
      MAlonzo.Code.Qfoundation.Qpropositions.du_is'45'trunc'45'is'45'prop_10
      (coe v0) (coe v1) (coe (\ v2 -> coe du_ex'45'falso_18 erased))
