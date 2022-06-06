{-# LANGUAGE BangPatterns, EmptyDataDecls, EmptyCase,
             ExistentialQuantification, ScopedTypeVariables,
             NoMonomorphismRestriction, RankNTypes, PatternSynonyms,
             OverloadedStrings #-}
module MAlonzo.Code.Qfoundation.QemptyZ45Ztypes where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.Qpropositions
import qualified MAlonzo.Code.Qfoundation.Qpropositions
import qualified MAlonzo.Code.Qfoundation.QraisingZ45ZuniverseZ45Zlevels

-- foundation.empty-types.raise-empty
d_raise'45'empty_6 :: MAlonzo.Code.Agda.Primitive.T_Level_14 -> ()
d_raise'45'empty_6 = erased
-- foundation.empty-types.equiv-raise-empty
d_equiv'45'raise'45'empty_12 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_equiv'45'raise'45'empty_12 ~v0 = du_equiv'45'raise'45'empty_12
du_equiv'45'raise'45'empty_12 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_equiv'45'raise'45'empty_12
  = coe
      MAlonzo.Code.Qfoundation.QraisingZ45ZuniverseZ45Zlevels.du_equiv'45'raise_50
-- foundation.empty-types.is-prop-is-empty
d_is'45'prop'45'is'45'empty_20 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.T_empty_4) ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.T_empty_4) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'prop'45'is'45'empty_20 v0 ~v1
  = du_is'45'prop'45'is'45'empty_20 v0
du_is'45'prop'45'is'45'empty_20 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.T_empty_4) ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.T_empty_4) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'prop'45'is'45'empty_20 v0
  = coe
      MAlonzo.Code.Qfoundation.Qpropositions.du_is'45'prop'45'function'45'type_192
      v0 ()
      (\ v1 ->
         coe
           MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.du_is'45'prop'45'empty_88)
-- foundation.empty-types.is-empty-Prop
d_is'45'empty'45'Prop_24 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'empty'45'Prop_24 v0 ~v1 = du_is'45'empty'45'Prop_24 v0
du_is'45'empty'45'Prop_24 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'empty'45'Prop_24 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      erased (coe du_is'45'prop'45'is'45'empty_20 (coe v0))
-- foundation.empty-types.is-nonempty-Prop
d_is'45'nonempty'45'Prop_32 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'nonempty'45'Prop_32 v0 ~v1
  = du_is'45'nonempty'45'Prop_32 v0
du_is'45'nonempty'45'Prop_32 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'nonempty'45'Prop_32 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      erased (coe du_is'45'prop'45'is'45'empty_20 (coe v0))
-- foundation.empty-types.is-empty-type-trunc-Prop
d_is'45'empty'45'type'45'trunc'45'Prop_42 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.T_empty_4) ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.T_empty_4
d_is'45'empty'45'type'45'trunc'45'Prop_42 = erased
-- foundation.empty-types.is-empty-type-trunc-Prop'
d_is'45'empty'45'type'45'trunc'45'Prop''_50 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.T_empty_4) ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.T_empty_4
d_is'45'empty'45'type'45'trunc'45'Prop''_50 = erased
-- foundation.empty-types.is-nonempty-is-inhabited
d_is'45'nonempty'45'is'45'inhabited_58 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  AgdaAny ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.T_empty_4) ->
  MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.T_empty_4
d_is'45'nonempty'45'is'45'inhabited_58 = erased
-- foundation.empty-types.is-prop-raise-empty
d_is'45'prop'45'raise'45'empty_70 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Qfoundation.QraisingZ45ZuniverseZ45Zlevels.T_raise_10 ->
  MAlonzo.Code.Qfoundation.QraisingZ45ZuniverseZ45Zlevels.T_raise_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'prop'45'raise'45'empty_70 ~v0
  = du_is'45'prop'45'raise'45'empty_70
du_is'45'prop'45'raise'45'empty_70 ::
  MAlonzo.Code.Qfoundation.QraisingZ45ZuniverseZ45Zlevels.T_raise_10 ->
  MAlonzo.Code.Qfoundation.QraisingZ45ZuniverseZ45Zlevels.T_raise_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'prop'45'raise'45'empty_70
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.Qpropositions.du_is'45'prop'45'equiv''_222
      (coe
         MAlonzo.Code.Qfoundation.QraisingZ45ZuniverseZ45Zlevels.du_equiv'45'raise_50)
      (\ v0 ->
         coe
           MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.du_is'45'prop'45'empty_88)
-- foundation.empty-types.raise-empty-Prop
d_raise'45'empty'45'Prop_76 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_raise'45'empty'45'Prop_76 ~v0 = du_raise'45'empty'45'Prop_76
du_raise'45'empty'45'Prop_76 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_raise'45'empty'45'Prop_76
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      erased (coe du_is'45'prop'45'raise'45'empty_70)
-- foundation.empty-types.is-empty-raise-empty
d_is'45'empty'45'raise'45'empty_84 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Qfoundation.QraisingZ45ZuniverseZ45Zlevels.T_raise_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.T_empty_4
d_is'45'empty'45'raise'45'empty_84 = erased
