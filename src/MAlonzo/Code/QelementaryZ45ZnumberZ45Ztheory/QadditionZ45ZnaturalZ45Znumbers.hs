{-# LANGUAGE BangPatterns, EmptyDataDecls, EmptyCase,
             ExistentialQuantification, ScopedTypeVariables,
             NoMonomorphismRestriction, RankNTypes, PatternSynonyms,
             OverloadedStrings #-}
module MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.QadditionZ45ZnaturalZ45Znumbers where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes
import qualified MAlonzo.Code.Qfoundation.QinjectiveZ45Zmaps

-- elementary-number-theory.addition-natural-numbers.add-ℕ
d_add'45'ℕ_4 :: Integer -> Integer -> Integer
d_add'45'ℕ_4 v0 v1
  = case coe v1 of
      0 -> coe v0
      _ -> let v2 = subInt (coe v1) (coe (1 :: Integer)) in
           coe
             addInt (coe (1 :: Integer)) (coe d_add'45'ℕ_4 (coe v0) (coe v2))
-- elementary-number-theory.addition-natural-numbers.add-ℕ'
d_add'45'ℕ''_12 :: Integer -> Integer -> Integer
d_add'45'ℕ''_12 v0 v1 = coe d_add'45'ℕ_4 (coe v1) (coe v0)
-- elementary-number-theory.addition-natural-numbers.ap-add-ℕ
d_ap'45'add'45'ℕ_26 ::
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_ap'45'add'45'ℕ_26 = erased
-- elementary-number-theory.addition-natural-numbers.right-unit-law-add-ℕ
d_right'45'unit'45'law'45'add'45'ℕ_34 ::
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_right'45'unit'45'law'45'add'45'ℕ_34 = erased
-- elementary-number-theory.addition-natural-numbers.left-unit-law-add-ℕ
d_left'45'unit'45'law'45'add'45'ℕ_40 ::
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_left'45'unit'45'law'45'add'45'ℕ_40 = erased
-- elementary-number-theory.addition-natural-numbers.left-successor-law-add-ℕ
d_left'45'successor'45'law'45'add'45'ℕ_48 ::
  Integer ->
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_left'45'successor'45'law'45'add'45'ℕ_48 = erased
-- elementary-number-theory.addition-natural-numbers.right-successor-law-add-ℕ
d_right'45'successor'45'law'45'add'45'ℕ_60 ::
  Integer ->
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_right'45'successor'45'law'45'add'45'ℕ_60 = erased
-- elementary-number-theory.addition-natural-numbers.associative-add-ℕ
d_associative'45'add'45'ℕ_72 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_associative'45'add'45'ℕ_72 = erased
-- elementary-number-theory.addition-natural-numbers.commutative-add-ℕ
d_commutative'45'add'45'ℕ_88 ::
  Integer ->
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_commutative'45'add'45'ℕ_88 = erased
-- elementary-number-theory.addition-natural-numbers.left-one-law-add-ℕ
d_left'45'one'45'law'45'add'45'ℕ_98 ::
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_left'45'one'45'law'45'add'45'ℕ_98 = erased
-- elementary-number-theory.addition-natural-numbers.right-one-law-add-ℕ
d_right'45'one'45'law'45'add'45'ℕ_104 ::
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_right'45'one'45'law'45'add'45'ℕ_104 = erased
-- elementary-number-theory.addition-natural-numbers.left-two-law-add-ℕ
d_left'45'two'45'law'45'add'45'ℕ_110 ::
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_left'45'two'45'law'45'add'45'ℕ_110 = erased
-- elementary-number-theory.addition-natural-numbers.right-two-law-add-ℕ
d_right'45'two'45'law'45'add'45'ℕ_116 ::
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_right'45'two'45'law'45'add'45'ℕ_116 = erased
-- elementary-number-theory.addition-natural-numbers.interchange-law-add-add-ℕ
d_interchange'45'law'45'add'45'add'45'ℕ_120 ::
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_interchange'45'law'45'add'45'add'45'ℕ_120 = erased
-- elementary-number-theory.addition-natural-numbers.is-injective-add-ℕ'
d_is'45'injective'45'add'45'ℕ''_124 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_is'45'injective'45'add'45'ℕ''_124 = erased
-- elementary-number-theory.addition-natural-numbers.is-injective-add-ℕ
d_is'45'injective'45'add'45'ℕ_132 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_is'45'injective'45'add'45'ℕ_132 = erased
-- elementary-number-theory.addition-natural-numbers.is-emb-add-ℕ
d_is'45'emb'45'add'45'ℕ_144 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'emb'45'add'45'ℕ_144 ~v0 = du_is'45'emb'45'add'45'ℕ_144
du_is'45'emb'45'add'45'ℕ_144 ::
  Integer ->
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'emb'45'add'45'ℕ_144
  = coe
      MAlonzo.Code.Qfoundation.QinjectiveZ45Zmaps.du_is'45'emb'45'is'45'injective_308
-- elementary-number-theory.addition-natural-numbers.is-emb-add-ℕ'
d_is'45'emb'45'add'45'ℕ''_150 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'emb'45'add'45'ℕ''_150 ~v0 = du_is'45'emb'45'add'45'ℕ''_150
du_is'45'emb'45'add'45'ℕ''_150 ::
  Integer ->
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'emb'45'add'45'ℕ''_150
  = coe
      MAlonzo.Code.Qfoundation.QinjectiveZ45Zmaps.du_is'45'emb'45'is'45'injective_308
-- elementary-number-theory.addition-natural-numbers.is-zero-right-is-zero-add-ℕ
d_is'45'zero'45'right'45'is'45'zero'45'add'45'ℕ_158 ::
  Integer ->
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_is'45'zero'45'right'45'is'45'zero'45'add'45'ℕ_158 = erased
-- elementary-number-theory.addition-natural-numbers.is-zero-left-is-zero-add-ℕ
d_is'45'zero'45'left'45'is'45'zero'45'add'45'ℕ_174 ::
  Integer ->
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_is'45'zero'45'left'45'is'45'zero'45'add'45'ℕ_174 = erased
-- elementary-number-theory.addition-natural-numbers.is-zero-summand-is-zero-sum-ℕ
d_is'45'zero'45'summand'45'is'45'zero'45'sum'45'ℕ_186 ::
  Integer ->
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'zero'45'summand'45'is'45'zero'45'sum'45'ℕ_186 ~v0 ~v1 ~v2
  = du_is'45'zero'45'summand'45'is'45'zero'45'sum'45'ℕ_186
du_is'45'zero'45'summand'45'is'45'zero'45'sum'45'ℕ_186 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'zero'45'summand'45'is'45'zero'45'sum'45'ℕ_186
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      erased erased
-- elementary-number-theory.addition-natural-numbers.is-zero-sum-is-zero-summand-ℕ
d_is'45'zero'45'sum'45'is'45'zero'45'summand'45'ℕ_198 ::
  Integer ->
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_is'45'zero'45'sum'45'is'45'zero'45'summand'45'ℕ_198 = erased
-- elementary-number-theory.addition-natural-numbers.neq-add-ℕ
d_neq'45'add'45'ℕ_204 ::
  Integer ->
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.T_empty_4
d_neq'45'add'45'ℕ_204 = erased
