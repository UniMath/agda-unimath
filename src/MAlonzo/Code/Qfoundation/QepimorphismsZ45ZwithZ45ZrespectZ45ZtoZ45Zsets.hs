{-# LANGUAGE BangPatterns, EmptyDataDecls, EmptyCase,
             ExistentialQuantification, ScopedTypeVariables,
             NoMonomorphismRestriction, RankNTypes, PatternSynonyms,
             OverloadedStrings #-}
module MAlonzo.Code.Qfoundation.QepimorphismsZ45ZwithZ45ZrespectZ45ZtoZ45Zsets where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.Qequivalences
import qualified MAlonzo.Code.QfoundationZ45Zcore.Qunivalence
import qualified MAlonzo.Code.Qfoundation.QexistentialZ45Zquantification
import qualified MAlonzo.Code.Qfoundation.QinjectiveZ45Zmaps
import qualified MAlonzo.Code.Qfoundation.QunitZ45Ztype

-- foundation.epimorphisms-with-respect-to-sets.is-epimorphism-Set
d_is'45'epimorphism'45'Set_16 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () -> () -> (AgdaAny -> AgdaAny) -> ()
d_is'45'epimorphism'45'Set_16 = erased
-- foundation.epimorphisms-with-respect-to-sets.is-epimorphism-is-surjective-Set
d_is'45'epimorphism'45'is'45'surjective'45'Set_36 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'epimorphism'45'is'45'surjective'45'Set_36 ~v0 ~v1 ~v2 ~v3
                                                  ~v4 ~v5 ~v6 ~v7
  = du_is'45'epimorphism'45'is'45'surjective'45'Set_36
du_is'45'epimorphism'45'is'45'surjective'45'Set_36 ::
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'epimorphism'45'is'45'surjective'45'Set_36
  = coe
      MAlonzo.Code.Qfoundation.QinjectiveZ45Zmaps.du_is'45'emb'45'is'45'injective_308
-- foundation.epimorphisms-with-respect-to-sets.is-surjective-is-epimorphism-Set
d_is'45'surjective'45'is'45'epimorphism'45'Set_64 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Agda.Primitive.T_Level_14 ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
   (AgdaAny -> AgdaAny) ->
   (AgdaAny -> AgdaAny) ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  AgdaAny -> AgdaAny
d_is'45'surjective'45'is'45'epimorphism'45'Set_64 ~v0 ~v1 ~v2 ~v3
                                                  ~v4 ~v5 ~v6
  = du_is'45'surjective'45'is'45'epimorphism'45'Set_64
du_is'45'surjective'45'is'45'epimorphism'45'Set_64 :: AgdaAny
du_is'45'surjective'45'is'45'epimorphism'45'Set_64
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_map'45'equiv_46
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.Qunivalence.du_equiv'45'eq_10)
      (coe MAlonzo.Code.Qfoundation.QunitZ45Ztype.du_raise'45'star_34)
-- foundation.epimorphisms-with-respect-to-sets._.g
d_g_84 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Agda.Primitive.T_Level_14 ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
   (AgdaAny -> AgdaAny) ->
   (AgdaAny -> AgdaAny) ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_g_84 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 = du_g_84
du_g_84 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_g_84
  = coe
      MAlonzo.Code.Qfoundation.QunitZ45Ztype.du_raise'45'unit'45'Prop_104
-- foundation.epimorphisms-with-respect-to-sets._.h
d_h_88 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Agda.Primitive.T_Level_14 ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
   (AgdaAny -> AgdaAny) ->
   (AgdaAny -> AgdaAny) ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_h_88 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 = du_h_88
du_h_88 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_h_88
  = coe
      MAlonzo.Code.Qfoundation.QexistentialZ45Zquantification.du_'8707''45'Prop_56
