{-# LANGUAGE BangPatterns, EmptyDataDecls, EmptyCase,
             ExistentialQuantification, ScopedTypeVariables,
             NoMonomorphismRestriction, RankNTypes, PatternSynonyms,
             OverloadedStrings #-}
module MAlonzo.Code.Qfoundation.QlocallyZ45ZsmallZ45Ztypes where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.Qequivalences
import qualified MAlonzo.Code.Qfoundation.QfunctionZ45Zextensionality
import qualified MAlonzo.Code.Qfoundation.Qpropositions
import qualified MAlonzo.Code.Qfoundation.QsmallZ45Ztypes
import qualified MAlonzo.Code.Qfoundation.Qunivalence

-- foundation.locally-small-types.is-locally-small
d_is'45'locally'45'small_10 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 -> () -> ()
d_is'45'locally'45'small_10 = erased
-- foundation.locally-small-types.is-locally-small-is-small
d_is'45'locally'45'small'45'is'45'small_26 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'locally'45'small'45'is'45'small_26 ~v0 ~v1 ~v2 v3 ~v4 ~v5
  = du_is'45'locally'45'small'45'is'45'small_26 v3
du_is'45'locally'45'small'45'is'45'small_26 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'locally'45'small'45'is'45'small_26 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      erased
      (coe
         seq (coe v0)
         (coe
            MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_equiv'45'ap_912))
-- foundation.locally-small-types.is-locally-small-is-prop
d_is'45'locally'45'small'45'is'45'prop_54 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'locally'45'small'45'is'45'prop_54 ~v0 ~v1 ~v2 v3 v4 v5
  = du_is'45'locally'45'small'45'is'45'prop_54 v3 v4 v5
du_is'45'locally'45'small'45'is'45'prop_54 ::
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'locally'45'small'45'is'45'prop_54 v0 v1 v2
  = coe
      MAlonzo.Code.Qfoundation.QsmallZ45Ztypes.du_is'45'small'45'is'45'contr_176
      (coe v0 v1 v2)
-- foundation.locally-small-types.is-locally-small-UU
d_is'45'locally'45'small'45'UU_66 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'locally'45'small'45'UU_66 v0 ~v1 ~v2
  = du_is'45'locally'45'small'45'UU_66 v0
du_is'45'locally'45'small'45'UU_66 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'locally'45'small'45'UU_66 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      erased
      (coe
         MAlonzo.Code.Qfoundation.Qunivalence.du_equiv'45'univalence_30
         (coe v0))
-- foundation.locally-small-types.is-locally-small-Π
d_is'45'locally'45'small'45'Π_90 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'locally'45'small'45'Π_90 v0 v1 v2 ~v3 ~v4 v5 v6 v7 v8
  = du_is'45'locally'45'small'45'Π_90 v0 v1 v2 v5 v6 v7 v8
du_is'45'locally'45'small'45'Π_90 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'locally'45'small'45'Π_90 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Qfoundation.QsmallZ45Ztypes.du_is'45'small'45'equiv_88
      (coe
         MAlonzo.Code.Qfoundation.QfunctionZ45Zextensionality.du_equiv'45'funext_60
         (coe v1) (coe v2) (coe v5) (coe v6))
      (coe
         MAlonzo.Code.Qfoundation.QsmallZ45Ztypes.du_is'45'small'45'Π_200
         (coe v0) (coe v3)
         (coe (\ v7 -> coe v4 v7 (coe v5 v7) (coe v6 v7))))
-- foundation.locally-small-types.is-prop-is-locally-small
d_is'45'prop'45'is'45'locally'45'small_110 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'prop'45'is'45'locally'45'small_110 ~v0 v1 ~v2
  = du_is'45'prop'45'is'45'locally'45'small_110 v1
du_is'45'prop'45'is'45'locally'45'small_110 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'prop'45'is'45'locally'45'small_110 v0
  = coe
      MAlonzo.Code.Qfoundation.Qpropositions.du_is'45'prop'45'Π_48 v0 ()
      (\ v1 ->
         coe
           MAlonzo.Code.Qfoundation.Qpropositions.du_is'45'prop'45'Π_48 v0 ()
           (\ v2 ->
              coe
                MAlonzo.Code.Qfoundation.QsmallZ45Ztypes.du_is'45'prop'45'is'45'small_264))
-- foundation.locally-small-types.is-locally-small-Prop
d_is'45'locally'45'small'45'Prop_126 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'locally'45'small'45'Prop_126 ~v0 v1 ~v2
  = du_is'45'locally'45'small'45'Prop_126 v1
du_is'45'locally'45'small'45'Prop_126 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'locally'45'small'45'Prop_126 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      erased (coe du_is'45'prop'45'is'45'locally'45'small_110 (coe v0))
