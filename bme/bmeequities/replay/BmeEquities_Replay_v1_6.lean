import Wire

/-!
# Bolsas y Mercados Españoles BME Equities Replay v1.6

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.BmeBmeequitiesReplayBmegateV16

/-- Security Status: one byte code -/
def SecurityStatus.codes : List UInt8 :=
  [0x31, 0x32]

inductive SecurityStatus where
  | active -- Active
  | inactiveProvissionalyAssumed -- Inactive Provissionaly Assumed
  | unlisted (byte : { byte : UInt8 // byte ∉ SecurityStatus.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace SecurityStatus

def toByte : SecurityStatus → UInt8
  | .active => 0x31
  | .inactiveProvissionalyAssumed => 0x32
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : SecurityStatus :=
  if byte = 0x31 then .active
  else .inactiveProvissionalyAssumed

def ofByte (byte : UInt8) : SecurityStatus :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : SecurityStatus) : ofByte value.toByte = value := by
  cases value with
  | active => decide
  | inactiveProvissionalyAssumed => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : SecurityStatus) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (SecurityStatus × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : SecurityStatus) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : SecurityStatus) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : SecurityStatus) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end SecurityStatus

/-- Exercise Style: one byte code -/
def ExerciseStyle.codes : List UInt8 :=
  [0x41, 0x45, 0x42, 0x4F]

inductive ExerciseStyle where
  | american -- American
  | european -- European
  | bermudas -- Bermudas
  | others -- Others
  | unlisted (byte : { byte : UInt8 // byte ∉ ExerciseStyle.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ExerciseStyle

def toByte : ExerciseStyle → UInt8
  | .american => 0x41
  | .european => 0x45
  | .bermudas => 0x42
  | .others => 0x4F
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ExerciseStyle :=
  if byte = 0x41 then .american
  else if byte = 0x45 then .european
  else if byte = 0x42 then .bermudas
  else .others

def ofByte (byte : UInt8) : ExerciseStyle :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ExerciseStyle) : ofByte value.toByte = value := by
  cases value with
  | american => decide
  | european => decide
  | bermudas => decide
  | others => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ExerciseStyle) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ExerciseStyle × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ExerciseStyle) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : ExerciseStyle) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : ExerciseStyle) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ExerciseStyle

/-- Put Or Call: one byte code -/
def PutOrCall.codes : List UInt8 :=
  [0x43, 0x50, 0x4F]

inductive PutOrCall where
  | call -- Call
  | put -- Put
  | other -- Other
  | unlisted (byte : { byte : UInt8 // byte ∉ PutOrCall.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace PutOrCall

def toByte : PutOrCall → UInt8
  | .call => 0x43
  | .put => 0x50
  | .other => 0x4F
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : PutOrCall :=
  if byte = 0x43 then .call
  else if byte = 0x50 then .put
  else .other

def ofByte (byte : UInt8) : PutOrCall :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : PutOrCall) : ofByte value.toByte = value := by
  cases value with
  | call => decide
  | put => decide
  | other => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : PutOrCall) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (PutOrCall × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : PutOrCall) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : PutOrCall) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : PutOrCall) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end PutOrCall

/-- Reference Trading Venue: one byte code -/
def ReferenceTradingVenue.codes : List UInt8 :=
  [0x31, 0x32, 0x34, 0x38]

inductive ReferenceTradingVenue where
  | valencia -- Valencia
  | bilbao -- Bilbao
  | barcelona -- Barcelona
  | madrid -- Madrid
  | unlisted (byte : { byte : UInt8 // byte ∉ ReferenceTradingVenue.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ReferenceTradingVenue

def toByte : ReferenceTradingVenue → UInt8
  | .valencia => 0x31
  | .bilbao => 0x32
  | .barcelona => 0x34
  | .madrid => 0x38
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ReferenceTradingVenue :=
  if byte = 0x31 then .valencia
  else if byte = 0x32 then .bilbao
  else if byte = 0x34 then .barcelona
  else .madrid

def ofByte (byte : UInt8) : ReferenceTradingVenue :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ReferenceTradingVenue) : ofByte value.toByte = value := by
  cases value with
  | valencia => decide
  | bilbao => decide
  | barcelona => decide
  | madrid => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ReferenceTradingVenue) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ReferenceTradingVenue × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ReferenceTradingVenue) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : ReferenceTradingVenue) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : ReferenceTradingVenue) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ReferenceTradingVenue

/-- Settlement System: one byte code -/
def SettlementSystem.codes : List UInt8 :=
  [0x46, 0x4C]

inductive SettlementSystem where
  | iberclear -- Iberclear
  | iberclearLatibex -- Iberclear Latibex
  | unlisted (byte : { byte : UInt8 // byte ∉ SettlementSystem.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace SettlementSystem

def toByte : SettlementSystem → UInt8
  | .iberclear => 0x46
  | .iberclearLatibex => 0x4C
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : SettlementSystem :=
  if byte = 0x46 then .iberclear
  else .iberclearLatibex

def ofByte (byte : UInt8) : SettlementSystem :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : SettlementSystem) : ofByte value.toByte = value := by
  cases value with
  | iberclear => decide
  | iberclearLatibex => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : SettlementSystem) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (SettlementSystem × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : SettlementSystem) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : SettlementSystem) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : SettlementSystem) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end SettlementSystem

/-- Nav Communication Term: one byte code -/
def NavCommunicationTerm.codes : List UInt8 :=
  [0x31, 0x32, 0x33]

inductive NavCommunicationTerm where
  | d1 -- D 1
  | d2 -- D 2
  | d3 -- D 3
  | unlisted (byte : { byte : UInt8 // byte ∉ NavCommunicationTerm.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace NavCommunicationTerm

def toByte : NavCommunicationTerm → UInt8
  | .d1 => 0x31
  | .d2 => 0x32
  | .d3 => 0x33
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : NavCommunicationTerm :=
  if byte = 0x31 then .d1
  else if byte = 0x32 then .d2
  else .d3

def ofByte (byte : UInt8) : NavCommunicationTerm :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : NavCommunicationTerm) : ofByte value.toByte = value := by
  cases value with
  | d1 => decide
  | d2 => decide
  | d3 => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : NavCommunicationTerm) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (NavCommunicationTerm × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : NavCommunicationTerm) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : NavCommunicationTerm) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : NavCommunicationTerm) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end NavCommunicationTerm

/-- Commodity Derivative Indicator: one byte code -/
def CommodityDerivativeIndicator.codes : List UInt8 :=
  [0x53, 0x4E, 0x44]

inductive CommodityDerivativeIndicator where
  | commodityDerivative -- Commodity Derivative
  | nonDerivative -- Non Derivative
  | derivative -- Derivative
  | unlisted (byte : { byte : UInt8 // byte ∉ CommodityDerivativeIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace CommodityDerivativeIndicator

def toByte : CommodityDerivativeIndicator → UInt8
  | .commodityDerivative => 0x53
  | .nonDerivative => 0x4E
  | .derivative => 0x44
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : CommodityDerivativeIndicator :=
  if byte = 0x53 then .commodityDerivative
  else if byte = 0x4E then .nonDerivative
  else .derivative

def ofByte (byte : UInt8) : CommodityDerivativeIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : CommodityDerivativeIndicator) : ofByte value.toByte = value := by
  cases value with
  | commodityDerivative => decide
  | nonDerivative => decide
  | derivative => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : CommodityDerivativeIndicator) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (CommodityDerivativeIndicator × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : CommodityDerivativeIndicator) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : CommodityDerivativeIndicator) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : CommodityDerivativeIndicator) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end CommodityDerivativeIndicator

/-- Exemption Situation: one byte code -/
def ExemptionSituation.codes : List UInt8 :=
  [0x30, 0x31, 0x32, 0x33]

inductive ExemptionSituation where
  | specialistsNonExempted -- Specialists Non Exempted
  | specialistsExemptedInTheBuySide -- Specialists Exempted In The Buy Side
  | specialistsExemptedInTheSellSide -- Specialists Exempted In The Sell Side
  | specialistsExemptedInBothSidesBuyAndSell -- Specialists Exempted In Both Sides Buy And Sell
  | unlisted (byte : { byte : UInt8 // byte ∉ ExemptionSituation.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ExemptionSituation

def toByte : ExemptionSituation → UInt8
  | .specialistsNonExempted => 0x30
  | .specialistsExemptedInTheBuySide => 0x31
  | .specialistsExemptedInTheSellSide => 0x32
  | .specialistsExemptedInBothSidesBuyAndSell => 0x33
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ExemptionSituation :=
  if byte = 0x30 then .specialistsNonExempted
  else if byte = 0x31 then .specialistsExemptedInTheBuySide
  else if byte = 0x32 then .specialistsExemptedInTheSellSide
  else .specialistsExemptedInBothSidesBuyAndSell

def ofByte (byte : UInt8) : ExemptionSituation :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ExemptionSituation) : ofByte value.toByte = value := by
  cases value with
  | specialistsNonExempted => decide
  | specialistsExemptedInTheBuySide => decide
  | specialistsExemptedInTheSellSide => decide
  | specialistsExemptedInBothSidesBuyAndSell => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ExemptionSituation) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ExemptionSituation × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ExemptionSituation) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : ExemptionSituation) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : ExemptionSituation) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ExemptionSituation

/-- Static Range Type: one byte code -/
def StaticRangeType.codes : List UInt8 :=
  [0x50, 0x54]

inductive StaticRangeType where
  | percentage -- Percentage
  | price -- Price
  | unlisted (byte : { byte : UInt8 // byte ∉ StaticRangeType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace StaticRangeType

def toByte : StaticRangeType → UInt8
  | .percentage => 0x50
  | .price => 0x54
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : StaticRangeType :=
  if byte = 0x50 then .percentage
  else .price

def ofByte (byte : UInt8) : StaticRangeType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : StaticRangeType) : ofByte value.toByte = value := by
  cases value with
  | percentage => decide
  | price => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : StaticRangeType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (StaticRangeType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : StaticRangeType) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : StaticRangeType) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : StaticRangeType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end StaticRangeType

/-- Side: one byte code -/
def Side.codes : List UInt8 :=
  [0x31, 0x32, 0x37, 0x3F]

inductive Side where
  | buy -- Buy
  | sell -- Sell
  | undisclosed -- Undisclosed
  | notspecified -- Notspecified
  | unlisted (byte : { byte : UInt8 // byte ∉ Side.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Side

def toByte : Side → UInt8
  | .buy => 0x31
  | .sell => 0x32
  | .undisclosed => 0x37
  | .notspecified => 0x3F
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Side :=
  if byte = 0x31 then .buy
  else if byte = 0x32 then .sell
  else if byte = 0x37 then .undisclosed
  else .notspecified

def ofByte (byte : UInt8) : Side :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Side) : ofByte value.toByte = value := by
  cases value with
  | buy => decide
  | sell => decide
  | undisclosed => decide
  | notspecified => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Side) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Side × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Side) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : Side) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : Side) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Side

/-- Trade Type: one byte code -/
def TradeType.codes : List UInt8 :=
  [0x4D, 0x58, 0x54, 0x48, 0x31, 0x32, 0x33, 0x34, 0x35, 0x36]

inductive TradeType where
  | market -- Market
  | cancellation -- Cancellation
  | tradeAmendment -- Trade Amendment
  | blockTrade -- Block Trade
  | communicatedApplication -- Communicated Application
  | authorisedApplicationTrades -- Authorised Application Trades
  | authorisedApplicationCorporateInterest -- Authorised Application Corporate Interest
  | authorisedApplicationExecutionOfContracts -- Authorised Application Execution Of Contracts
  | authorisedApplicationOtherCauses -- Authorised Application Other Causes
  | validationCommunicated -- Validation Communicated
  | unlisted (byte : { byte : UInt8 // byte ∉ TradeType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TradeType

def toByte : TradeType → UInt8
  | .market => 0x4D
  | .cancellation => 0x58
  | .tradeAmendment => 0x54
  | .blockTrade => 0x48
  | .communicatedApplication => 0x31
  | .authorisedApplicationTrades => 0x32
  | .authorisedApplicationCorporateInterest => 0x33
  | .authorisedApplicationExecutionOfContracts => 0x34
  | .authorisedApplicationOtherCauses => 0x35
  | .validationCommunicated => 0x36
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TradeType :=
  if byte = 0x4D then .market
  else if byte = 0x58 then .cancellation
  else if byte = 0x54 then .tradeAmendment
  else if byte = 0x48 then .blockTrade
  else if byte = 0x31 then .communicatedApplication
  else if byte = 0x32 then .authorisedApplicationTrades
  else if byte = 0x33 then .authorisedApplicationCorporateInterest
  else if byte = 0x34 then .authorisedApplicationExecutionOfContracts
  else if byte = 0x35 then .authorisedApplicationOtherCauses
  else .validationCommunicated

def ofByte (byte : UInt8) : TradeType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TradeType) : ofByte value.toByte = value := by
  cases value with
  | market => decide
  | cancellation => decide
  | tradeAmendment => decide
  | blockTrade => decide
  | communicatedApplication => decide
  | authorisedApplicationTrades => decide
  | authorisedApplicationCorporateInterest => decide
  | authorisedApplicationExecutionOfContracts => decide
  | authorisedApplicationOtherCauses => decide
  | validationCommunicated => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : TradeType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (TradeType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : TradeType) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : TradeType) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : TradeType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end TradeType

/-- Designation: one byte code -/
def Designation.codes : List UInt8 :=
  [0x31, 0x32, 0x33, 0x34, 0x35, 0x36, 0x37, 0x38, 0x43]

inductive Designation where
  | tradeDuringOpenMarket -- Trade During Open Market
  | tradeDuringOpeningAuction -- Trade During Opening Auction
  | tradeDuringClosingAuction -- Trade During Closing Auction
  | tradeDuringVolatilityAuction -- Trade During Volatility Auction
  | tradeDuringManualAuction -- Trade During Manual Auction
  | tradeDuringOpeningAuctionExtension -- Trade During Opening Auction Extension
  | tradeDuringClosingAuctionExtension -- Trade During Closing Auction Extension
  | tradeDuringTalPeriod -- Trade During Tal Period
  | tradeInSpainAtMidDarkBook -- Trade In Spain At Mid Dark Book
  | unlisted (byte : { byte : UInt8 // byte ∉ Designation.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Designation

def toByte : Designation → UInt8
  | .tradeDuringOpenMarket => 0x31
  | .tradeDuringOpeningAuction => 0x32
  | .tradeDuringClosingAuction => 0x33
  | .tradeDuringVolatilityAuction => 0x34
  | .tradeDuringManualAuction => 0x35
  | .tradeDuringOpeningAuctionExtension => 0x36
  | .tradeDuringClosingAuctionExtension => 0x37
  | .tradeDuringTalPeriod => 0x38
  | .tradeInSpainAtMidDarkBook => 0x43
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Designation :=
  if byte = 0x31 then .tradeDuringOpenMarket
  else if byte = 0x32 then .tradeDuringOpeningAuction
  else if byte = 0x33 then .tradeDuringClosingAuction
  else if byte = 0x34 then .tradeDuringVolatilityAuction
  else if byte = 0x35 then .tradeDuringManualAuction
  else if byte = 0x36 then .tradeDuringOpeningAuctionExtension
  else if byte = 0x37 then .tradeDuringClosingAuctionExtension
  else if byte = 0x38 then .tradeDuringTalPeriod
  else .tradeInSpainAtMidDarkBook

def ofByte (byte : UInt8) : Designation :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Designation) : ofByte value.toByte = value := by
  cases value with
  | tradeDuringOpenMarket => decide
  | tradeDuringOpeningAuction => decide
  | tradeDuringClosingAuction => decide
  | tradeDuringVolatilityAuction => decide
  | tradeDuringManualAuction => decide
  | tradeDuringOpeningAuctionExtension => decide
  | tradeDuringClosingAuctionExtension => decide
  | tradeDuringTalPeriod => decide
  | tradeInSpainAtMidDarkBook => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Designation) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Designation × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Designation) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : Designation) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : Designation) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Designation

/-- Market Mechanism: one byte code -/
def MarketMechanism.codes : List UInt8 :=
  [0x30, 0x34, 0x31, 0x35]

inductive MarketMechanism where
  | centralLimitOrderBook -- Central Limit Order Book
  | darkOrderBook -- Dark Order Book
  | offBookMessagingTrading -- Off Book Messaging Trading
  | periodicAuction -- Periodic Auction
  | unlisted (byte : { byte : UInt8 // byte ∉ MarketMechanism.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace MarketMechanism

def toByte : MarketMechanism → UInt8
  | .centralLimitOrderBook => 0x30
  | .darkOrderBook => 0x34
  | .offBookMessagingTrading => 0x31
  | .periodicAuction => 0x35
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : MarketMechanism :=
  if byte = 0x30 then .centralLimitOrderBook
  else if byte = 0x34 then .darkOrderBook
  else if byte = 0x31 then .offBookMessagingTrading
  else .periodicAuction

def ofByte (byte : UInt8) : MarketMechanism :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : MarketMechanism) : ofByte value.toByte = value := by
  cases value with
  | centralLimitOrderBook => decide
  | darkOrderBook => decide
  | offBookMessagingTrading => decide
  | periodicAuction => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : MarketMechanism) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (MarketMechanism × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : MarketMechanism) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : MarketMechanism) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : MarketMechanism) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end MarketMechanism

/-- Buyer Bolsa Code: one byte code -/
def BuyerBolsaCode.codes : List UInt8 :=
  [0x33, 0x34, 0x35, 0x36]

inductive BuyerBolsaCode where
  | valencia -- Valencia
  | barcelona -- Barcelona
  | bilbao -- Bilbao
  | madrid -- Madrid
  | unlisted (byte : { byte : UInt8 // byte ∉ BuyerBolsaCode.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace BuyerBolsaCode

def toByte : BuyerBolsaCode → UInt8
  | .valencia => 0x33
  | .barcelona => 0x34
  | .bilbao => 0x35
  | .madrid => 0x36
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : BuyerBolsaCode :=
  if byte = 0x33 then .valencia
  else if byte = 0x34 then .barcelona
  else if byte = 0x35 then .bilbao
  else .madrid

def ofByte (byte : UInt8) : BuyerBolsaCode :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : BuyerBolsaCode) : ofByte value.toByte = value := by
  cases value with
  | valencia => decide
  | barcelona => decide
  | bilbao => decide
  | madrid => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : BuyerBolsaCode) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (BuyerBolsaCode × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : BuyerBolsaCode) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : BuyerBolsaCode) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : BuyerBolsaCode) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end BuyerBolsaCode

/-- Transaction Category: one byte code -/
def TransactionCategory.codes : List UInt8 :=
  [0x20, 0x44]

inductive TransactionCategory where
  | normalCategory -- Normal Category
  | darkTrade -- Dark Trade
  | unlisted (byte : { byte : UInt8 // byte ∉ TransactionCategory.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TransactionCategory

def toByte : TransactionCategory → UInt8
  | .normalCategory => 0x20
  | .darkTrade => 0x44
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TransactionCategory :=
  if byte = 0x20 then .normalCategory
  else .darkTrade

def ofByte (byte : UInt8) : TransactionCategory :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TransactionCategory) : ofByte value.toByte = value := by
  cases value with
  | normalCategory => decide
  | darkTrade => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : TransactionCategory) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (TransactionCategory × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : TransactionCategory) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : TransactionCategory) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : TransactionCategory) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end TransactionCategory

/-- Bencrfpt Flag: one byte code -/
def BencrfptFlag.codes : List UInt8 :=
  [0x20, 0x36, 0x33, 0x43, 0x4D]

inductive BencrfptFlag where
  | normalTrade -- Normal Trade
  | benchmarkTradeBenc -- Benchmark Trade Benc
  | referencePriceTradeRfpt -- Reference Price Trade Rfpt
  | contingencyTradeCont -- Contingency Trade Cont
  | bencCont -- Benc Cont
  | unlisted (byte : { byte : UInt8 // byte ∉ BencrfptFlag.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace BencrfptFlag

def toByte : BencrfptFlag → UInt8
  | .normalTrade => 0x20
  | .benchmarkTradeBenc => 0x36
  | .referencePriceTradeRfpt => 0x33
  | .contingencyTradeCont => 0x43
  | .bencCont => 0x4D
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : BencrfptFlag :=
  if byte = 0x20 then .normalTrade
  else if byte = 0x36 then .benchmarkTradeBenc
  else if byte = 0x33 then .referencePriceTradeRfpt
  else if byte = 0x43 then .contingencyTradeCont
  else .bencCont

def ofByte (byte : UInt8) : BencrfptFlag :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : BencrfptFlag) : ofByte value.toByte = value := by
  cases value with
  | normalTrade => decide
  | benchmarkTradeBenc => decide
  | referencePriceTradeRfpt => decide
  | contingencyTradeCont => decide
  | bencCont => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : BencrfptFlag) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (BencrfptFlag × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : BencrfptFlag) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : BencrfptFlag) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : BencrfptFlag) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end BencrfptFlag

/-- Trade Price Condition: one byte code -/
def TradePriceCondition.codes : List UInt8 :=
  [0x20, 0x35, 0x36]

inductive TradePriceCondition where
  | plainVanillaTrade -- Plain Vanilla Trade
  | nonPriceFormingTradeFormerlyDefinedAsATechnicalTradeNpft -- Non Price Forming Trade Formerly Defined As A Technical Trade Npft
  | tradeNotContributingToThePriceDiscoveryProcessFormerlyDefinedAsATechnicalTradeTncpToBeDiscontinuedAsOf1StJanuary2024 -- Trade Not Contributing To The Price Discovery Process Formerly Defined As A Technical Trade Tncp To Be Discontinued As Of 1 St January 2024
  | unlisted (byte : { byte : UInt8 // byte ∉ TradePriceCondition.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TradePriceCondition

def toByte : TradePriceCondition → UInt8
  | .plainVanillaTrade => 0x20
  | .nonPriceFormingTradeFormerlyDefinedAsATechnicalTradeNpft => 0x35
  | .tradeNotContributingToThePriceDiscoveryProcessFormerlyDefinedAsATechnicalTradeTncpToBeDiscontinuedAsOf1StJanuary2024 => 0x36
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TradePriceCondition :=
  if byte = 0x20 then .plainVanillaTrade
  else if byte = 0x35 then .nonPriceFormingTradeFormerlyDefinedAsATechnicalTradeNpft
  else .tradeNotContributingToThePriceDiscoveryProcessFormerlyDefinedAsATechnicalTradeTncpToBeDiscontinuedAsOf1StJanuary2024

def ofByte (byte : UInt8) : TradePriceCondition :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TradePriceCondition) : ofByte value.toByte = value := by
  cases value with
  | plainVanillaTrade => decide
  | nonPriceFormingTradeFormerlyDefinedAsATechnicalTradeNpft => decide
  | tradeNotContributingToThePriceDiscoveryProcessFormerlyDefinedAsATechnicalTradeTncpToBeDiscontinuedAsOf1StJanuary2024 => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : TradePriceCondition) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (TradePriceCondition × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : TradePriceCondition) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : TradePriceCondition) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : TradePriceCondition) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end TradePriceCondition

/-- Pre Trade Transparency Waiver: one byte code -/
def PreTradeTransparencyWaiver.codes : List UInt8 :=
  [0x30, 0x31, 0x32]

inductive PreTradeTransparencyWaiver where
  | negotiatedTradeInLiquidFinancialInstrumentsNliq -- Negotiated Trade In Liquid Financial Instruments Nliq
  | negotiatedTradeInIlliquidFinancialInstrumentsOilq -- Negotiated Trade In Illiquid Financial Instruments Oilq
  | negotiatedTradeSubjectToConditionsOtherThanTheCurrentMarketPricePric -- Negotiated Trade Subject To Conditions Other Than The Current Market Price Pric
  | unlisted (byte : { byte : UInt8 // byte ∉ PreTradeTransparencyWaiver.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace PreTradeTransparencyWaiver

def toByte : PreTradeTransparencyWaiver → UInt8
  | .negotiatedTradeInLiquidFinancialInstrumentsNliq => 0x30
  | .negotiatedTradeInIlliquidFinancialInstrumentsOilq => 0x31
  | .negotiatedTradeSubjectToConditionsOtherThanTheCurrentMarketPricePric => 0x32
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : PreTradeTransparencyWaiver :=
  if byte = 0x30 then .negotiatedTradeInLiquidFinancialInstrumentsNliq
  else if byte = 0x31 then .negotiatedTradeInIlliquidFinancialInstrumentsOilq
  else .negotiatedTradeSubjectToConditionsOtherThanTheCurrentMarketPricePric

def ofByte (byte : UInt8) : PreTradeTransparencyWaiver :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : PreTradeTransparencyWaiver) : ofByte value.toByte = value := by
  cases value with
  | negotiatedTradeInLiquidFinancialInstrumentsNliq => decide
  | negotiatedTradeInIlliquidFinancialInstrumentsOilq => decide
  | negotiatedTradeSubjectToConditionsOtherThanTheCurrentMarketPricePric => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : PreTradeTransparencyWaiver) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (PreTradeTransparencyWaiver × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : PreTradeTransparencyWaiver) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : PreTradeTransparencyWaiver) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : PreTradeTransparencyWaiver) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end PreTradeTransparencyWaiver

/-- Deferral Waiver: one byte code -/
def DeferralWaiver.codes : List UInt8 :=
  [0x20]

inductive DeferralWaiver where
  | immediatePublication -- Immediate Publication
  | unlisted (byte : { byte : UInt8 // byte ∉ DeferralWaiver.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace DeferralWaiver

def toByte : DeferralWaiver → UInt8
  | .immediatePublication => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (_ : UInt8) : DeferralWaiver :=
  .immediatePublication

def ofByte (byte : UInt8) : DeferralWaiver :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : DeferralWaiver) : ofByte value.toByte = value := by
  cases value with
  | immediatePublication => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : DeferralWaiver) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (DeferralWaiver × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : DeferralWaiver) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : DeferralWaiver) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : DeferralWaiver) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end DeferralWaiver

/-- Sicav Fund Counterparty Side: one byte code -/
def SicavFundCounterpartySide.codes : List UInt8 :=
  [0x31, 0x32, 0x20]

inductive SicavFundCounterpartySide where
  | buyer -- Buyer
  | seller -- Seller
  | na -- Na
  | unlisted (byte : { byte : UInt8 // byte ∉ SicavFundCounterpartySide.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace SicavFundCounterpartySide

def toByte : SicavFundCounterpartySide → UInt8
  | .buyer => 0x31
  | .seller => 0x32
  | .na => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : SicavFundCounterpartySide :=
  if byte = 0x31 then .buyer
  else if byte = 0x32 then .seller
  else .na

def ofByte (byte : UInt8) : SicavFundCounterpartySide :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : SicavFundCounterpartySide) : ofByte value.toByte = value := by
  cases value with
  | buyer => decide
  | seller => decide
  | na => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : SicavFundCounterpartySide) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (SicavFundCounterpartySide × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : SicavFundCounterpartySide) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : SicavFundCounterpartySide) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : SicavFundCounterpartySide) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end SicavFundCounterpartySide

/-- Amended Trade Type: one byte code -/
def AmendedTradeType.codes : List UInt8 :=
  [0x4D, 0x58, 0x54, 0x48, 0x31, 0x32, 0x33, 0x34, 0x35, 0x36]

inductive AmendedTradeType where
  | market -- Market
  | cancellation -- Cancellation
  | tradeAmendment -- Trade Amendment
  | blockTrade -- Block Trade
  | communicatedApplication -- Communicated Application
  | authorisedApplicationTrades -- Authorised Application Trades
  | authorisedApplicationCorporateInterest -- Authorised Application Corporate Interest
  | authorisedApplicationExecutionOfContracts -- Authorised Application Execution Of Contracts
  | authorisedApplicationOtherCauses -- Authorised Application Other Causes
  | validationCommunicated -- Validation Communicated
  | unlisted (byte : { byte : UInt8 // byte ∉ AmendedTradeType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace AmendedTradeType

def toByte : AmendedTradeType → UInt8
  | .market => 0x4D
  | .cancellation => 0x58
  | .tradeAmendment => 0x54
  | .blockTrade => 0x48
  | .communicatedApplication => 0x31
  | .authorisedApplicationTrades => 0x32
  | .authorisedApplicationCorporateInterest => 0x33
  | .authorisedApplicationExecutionOfContracts => 0x34
  | .authorisedApplicationOtherCauses => 0x35
  | .validationCommunicated => 0x36
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : AmendedTradeType :=
  if byte = 0x4D then .market
  else if byte = 0x58 then .cancellation
  else if byte = 0x54 then .tradeAmendment
  else if byte = 0x48 then .blockTrade
  else if byte = 0x31 then .communicatedApplication
  else if byte = 0x32 then .authorisedApplicationTrades
  else if byte = 0x33 then .authorisedApplicationCorporateInterest
  else if byte = 0x34 then .authorisedApplicationExecutionOfContracts
  else if byte = 0x35 then .authorisedApplicationOtherCauses
  else .validationCommunicated

def ofByte (byte : UInt8) : AmendedTradeType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : AmendedTradeType) : ofByte value.toByte = value := by
  cases value with
  | market => decide
  | cancellation => decide
  | tradeAmendment => decide
  | blockTrade => decide
  | communicatedApplication => decide
  | authorisedApplicationTrades => decide
  | authorisedApplicationCorporateInterest => decide
  | authorisedApplicationExecutionOfContracts => decide
  | authorisedApplicationOtherCauses => decide
  | validationCommunicated => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : AmendedTradeType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (AmendedTradeType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : AmendedTradeType) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : AmendedTradeType) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : AmendedTradeType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end AmendedTradeType

/-- Logon Response Message: 26 bytes -/
structure LogonResponseMessage where
  sequenceNumber : BitVec 32
  heartBtInt : BitVec 8
  protocolVersion : Alpha 6
  testProductionInd : Alpha 1
  environmentCode : Alpha 2
  sessionDate : BitVec 32
  expectedSequenceNumber : BitVec 32
  sequenceNumberTo : BitVec 32
  deriving DecidableEq, Repr

namespace LogonResponseMessage

def encode (message : LogonResponseMessage) : List UInt8 :=
  encodeUIntLE 4 message.sequenceNumber
    ++ (encodeUIntLE 1 message.heartBtInt
    ++ (Alpha.encode message.protocolVersion
    ++ (Alpha.encode message.testProductionInd
    ++ (Alpha.encode message.environmentCode
    ++ (encodeUIntLE 4 message.sessionDate
    ++ (encodeUIntLE 4 message.expectedSequenceNumber
    ++ (encodeUIntLE 4 message.sequenceNumberTo)))))))

def decode (bytes : List UInt8) : Option (LogonResponseMessage × List UInt8) := do
  let (sequenceNumber, bytes) ← decodeUIntLE 4 bytes
  let (heartBtInt, bytes) ← decodeUIntLE 1 bytes
  let (protocolVersion, bytes) ← Alpha.decode 6 bytes
  let (testProductionInd, bytes) ← Alpha.decode 1 bytes
  let (environmentCode, bytes) ← Alpha.decode 2 bytes
  let (sessionDate, bytes) ← decodeUIntLE 4 bytes
  let (expectedSequenceNumber, bytes) ← decodeUIntLE 4 bytes
  let (sequenceNumberTo, bytes) ← decodeUIntLE 4 bytes
  pure ({ sequenceNumber, heartBtInt, protocolVersion, testProductionInd, environmentCode, sessionDate, expectedSequenceNumber, sequenceNumberTo }, bytes)

@[simp] theorem encode_length (message : LogonResponseMessage) : (encode message).length = 26 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : LogonResponseMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LogonResponseMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end LogonResponseMessage

/-- Logout Response Message: 5 bytes -/
structure LogoutResponseMessage where
  sequenceNumber : BitVec 32
  logoutReason : BitVec 8
  deriving DecidableEq, Repr

namespace LogoutResponseMessage

def encode (message : LogoutResponseMessage) : List UInt8 :=
  encodeUIntLE 4 message.sequenceNumber
    ++ (encodeUIntLE 1 message.logoutReason)

def decode (bytes : List UInt8) : Option (LogoutResponseMessage × List UInt8) := do
  let (sequenceNumber, bytes) ← decodeUIntLE 4 bytes
  let (logoutReason, bytes) ← decodeUIntLE 1 bytes
  pure ({ sequenceNumber, logoutReason }, bytes)

@[simp] theorem encode_length (message : LogoutResponseMessage) : (encode message).length = 5 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : LogoutResponseMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LogoutResponseMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end LogoutResponseMessage

/-- Heartbeat Message: 4 bytes -/
structure HeartbeatMessage where
  sequenceNumber : BitVec 32
  deriving DecidableEq, Repr

namespace HeartbeatMessage

def encode (message : HeartbeatMessage) : List UInt8 :=
  encodeUIntLE 4 message.sequenceNumber

def decode (bytes : List UInt8) : Option (HeartbeatMessage × List UInt8) := do
  let (sequenceNumber, bytes) ← decodeUIntLE 4 bytes
  pure ({ sequenceNumber }, bytes)

@[simp] theorem encode_length (message : HeartbeatMessage) : (encode message).length = 4 := by
  unfold encode
  simp only [encodeUIntLE_length]

theorem encode_length_pos (message : HeartbeatMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : HeartbeatMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end HeartbeatMessage

/-- Network Status Message: 5 bytes -/
structure NetworkStatusMessage where
  sequenceNumber : BitVec 32
  networkStatusValue : BitVec 8
  deriving DecidableEq, Repr

namespace NetworkStatusMessage

def encode (message : NetworkStatusMessage) : List UInt8 :=
  encodeUIntLE 4 message.sequenceNumber
    ++ (encodeUIntLE 1 message.networkStatusValue)

def decode (bytes : List UInt8) : Option (NetworkStatusMessage × List UInt8) := do
  let (sequenceNumber, bytes) ← decodeUIntLE 4 bytes
  let (networkStatusValue, bytes) ← decodeUIntLE 1 bytes
  pure ({ sequenceNumber, networkStatusValue }, bytes)

@[simp] theorem encode_length (message : NetworkStatusMessage) : (encode message).length = 5 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : NetworkStatusMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : NetworkStatusMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end NetworkStatusMessage

/-- Logon Message: 53 bytes -/
structure LogonMessage where
  username : Alpha 7
  password : Alpha 10
  softwareName : Alpha 25
  expectedSequenceNumber : BitVec 32
  subscriptions : BitVec 8
  protocolVersion : Alpha 6
  deriving DecidableEq, Repr

namespace LogonMessage

def encode (message : LogonMessage) : List UInt8 :=
  Alpha.encode message.username
    ++ (Alpha.encode message.password
    ++ (Alpha.encode message.softwareName
    ++ (encodeUIntLE 4 message.expectedSequenceNumber
    ++ (encodeUIntLE 1 message.subscriptions
    ++ (Alpha.encode message.protocolVersion)))))

def decode (bytes : List UInt8) : Option (LogonMessage × List UInt8) := do
  let (username, bytes) ← Alpha.decode 7 bytes
  let (password, bytes) ← Alpha.decode 10 bytes
  let (softwareName, bytes) ← Alpha.decode 25 bytes
  let (expectedSequenceNumber, bytes) ← decodeUIntLE 4 bytes
  let (subscriptions, bytes) ← decodeUIntLE 1 bytes
  let (protocolVersion, bytes) ← Alpha.decode 6 bytes
  pure ({ username, password, softwareName, expectedSequenceNumber, subscriptions, protocolVersion }, bytes)

@[simp] theorem encode_length (message : LogonMessage) : (encode message).length = 53 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : LogonMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LogonMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end LogonMessage

/-- Reject Message: 70 bytes -/
structure RejectMessage where
  sequenceNumber : BitVec 32
  sessionRejectReason : BitVec 8
  text : Alpha 58
  msgRejectedReference : Alpha 7
  deriving DecidableEq, Repr

namespace RejectMessage

def encode (message : RejectMessage) : List UInt8 :=
  encodeUIntLE 4 message.sequenceNumber
    ++ (encodeUIntLE 1 message.sessionRejectReason
    ++ (Alpha.encode message.text
    ++ (Alpha.encode message.msgRejectedReference)))

def decode (bytes : List UInt8) : Option (RejectMessage × List UInt8) := do
  let (sequenceNumber, bytes) ← decodeUIntLE 4 bytes
  let (sessionRejectReason, bytes) ← decodeUIntLE 1 bytes
  let (text, bytes) ← Alpha.decode 58 bytes
  let (msgRejectedReference, bytes) ← Alpha.decode 7 bytes
  pure ({ sequenceNumber, sessionRejectReason, text, msgRejectedReference }, bytes)

@[simp] theorem encode_length (message : RejectMessage) : (encode message).length = 70 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : RejectMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : RejectMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end RejectMessage

/-- Replay Request Message: 8 bytes -/
structure ReplayRequestMessage where
  sequenceNumberFrom : BitVec 32
  sequenceNumberTo : BitVec 32
  deriving DecidableEq, Repr

namespace ReplayRequestMessage

def encode (message : ReplayRequestMessage) : List UInt8 :=
  encodeUIntLE 4 message.sequenceNumberFrom
    ++ (encodeUIntLE 4 message.sequenceNumberTo)

def decode (bytes : List UInt8) : Option (ReplayRequestMessage × List UInt8) := do
  let (sequenceNumberFrom, bytes) ← decodeUIntLE 4 bytes
  let (sequenceNumberTo, bytes) ← decodeUIntLE 4 bytes
  pure ({ sequenceNumberFrom, sequenceNumberTo }, bytes)

@[simp] theorem encode_length (message : ReplayRequestMessage) : (encode message).length = 8 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : ReplayRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ReplayRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end ReplayRequestMessage

/-- Replay Request Ack Nack Message: 17 bytes -/
structure ReplayRequestAckNackMessage where
  sequenceNumber : BitVec 32
  sequenceNumberFrom : BitVec 32
  sequenceNumberTo : BitVec 32
  requestId : BitVec 32
  status : BitVec 8
  deriving DecidableEq, Repr

namespace ReplayRequestAckNackMessage

def encode (message : ReplayRequestAckNackMessage) : List UInt8 :=
  encodeUIntLE 4 message.sequenceNumber
    ++ (encodeUIntLE 4 message.sequenceNumberFrom
    ++ (encodeUIntLE 4 message.sequenceNumberTo
    ++ (encodeUIntLE 4 message.requestId
    ++ (encodeUIntLE 1 message.status))))

def decode (bytes : List UInt8) : Option (ReplayRequestAckNackMessage × List UInt8) := do
  let (sequenceNumber, bytes) ← decodeUIntLE 4 bytes
  let (sequenceNumberFrom, bytes) ← decodeUIntLE 4 bytes
  let (sequenceNumberTo, bytes) ← decodeUIntLE 4 bytes
  let (requestId, bytes) ← decodeUIntLE 4 bytes
  let (status, bytes) ← decodeUIntLE 1 bytes
  pure ({ sequenceNumber, sequenceNumberFrom, sequenceNumberTo, requestId, status }, bytes)

@[simp] theorem encode_length (message : ReplayRequestAckNackMessage) : (encode message).length = 17 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : ReplayRequestAckNackMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ReplayRequestAckNackMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end ReplayRequestAckNackMessage

/-- Trading Session Status Message: 15 bytes -/
structure TradingSessionStatusMessage where
  sequenceNumber : BitVec 32
  tradingSessionId : BitVec 8
  tradingSessionSubId : BitVec 8
  tradSesStatus : BitVec 8
  transactionDateAndTime : BitVec 64
  deriving DecidableEq, Repr

namespace TradingSessionStatusMessage

def encode (message : TradingSessionStatusMessage) : List UInt8 :=
  encodeUIntLE 4 message.sequenceNumber
    ++ (encodeUIntLE 1 message.tradingSessionId
    ++ (encodeUIntLE 1 message.tradingSessionSubId
    ++ (encodeUIntLE 1 message.tradSesStatus
    ++ (encodeUIntLE 8 message.transactionDateAndTime))))

def decode (bytes : List UInt8) : Option (TradingSessionStatusMessage × List UInt8) := do
  let (sequenceNumber, bytes) ← decodeUIntLE 4 bytes
  let (tradingSessionId, bytes) ← decodeUIntLE 1 bytes
  let (tradingSessionSubId, bytes) ← decodeUIntLE 1 bytes
  let (tradSesStatus, bytes) ← decodeUIntLE 1 bytes
  let (transactionDateAndTime, bytes) ← decodeUIntLE 8 bytes
  pure ({ sequenceNumber, tradingSessionId, tradingSessionSubId, tradSesStatus, transactionDateAndTime }, bytes)

@[simp] theorem encode_length (message : TradingSessionStatusMessage) : (encode message).length = 15 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : TradingSessionStatusMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradingSessionStatusMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end TradingSessionStatusMessage

/-- News Message: 82 bytes -/
structure NewsMessage where
  sequenceNumber : BitVec 32
  newsText : Alpha 78
  deriving DecidableEq, Repr

namespace NewsMessage

def encode (message : NewsMessage) : List UInt8 :=
  encodeUIntLE 4 message.sequenceNumber
    ++ (Alpha.encode message.newsText)

def decode (bytes : List UInt8) : Option (NewsMessage × List UInt8) := do
  let (sequenceNumber, bytes) ← decodeUIntLE 4 bytes
  let (newsText, bytes) ← Alpha.decode 78 bytes
  pure ({ sequenceNumber, newsText }, bytes)

@[simp] theorem encode_length (message : NewsMessage) : (encode message).length = 82 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : NewsMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : NewsMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end NewsMessage

/-- Security List Cancellation Report Message: 50 bytes -/
structure SecurityListCancellationReportMessage where
  sequenceNumber : BitVec 32
  marketId : Alpha 4
  marketSegmentId : Alpha 4
  securityCode : BitVec 32
  symbol : Alpha 22
  symbolIsin : Alpha 12
  deriving DecidableEq, Repr

namespace SecurityListCancellationReportMessage

def encode (message : SecurityListCancellationReportMessage) : List UInt8 :=
  encodeUIntLE 4 message.sequenceNumber
    ++ (Alpha.encode message.marketId
    ++ (Alpha.encode message.marketSegmentId
    ++ (encodeUIntLE 4 message.securityCode
    ++ (Alpha.encode message.symbol
    ++ (Alpha.encode message.symbolIsin)))))

def decode (bytes : List UInt8) : Option (SecurityListCancellationReportMessage × List UInt8) := do
  let (sequenceNumber, bytes) ← decodeUIntLE 4 bytes
  let (marketId, bytes) ← Alpha.decode 4 bytes
  let (marketSegmentId, bytes) ← Alpha.decode 4 bytes
  let (securityCode, bytes) ← decodeUIntLE 4 bytes
  let (symbol, bytes) ← Alpha.decode 22 bytes
  let (symbolIsin, bytes) ← Alpha.decode 12 bytes
  pure ({ sequenceNumber, marketId, marketSegmentId, securityCode, symbol, symbolIsin }, bytes)

@[simp] theorem encode_length (message : SecurityListCancellationReportMessage) : (encode message).length = 50 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : SecurityListCancellationReportMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SecurityListCancellationReportMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end SecurityListCancellationReportMessage

/-- Statistics Message: 18 bytes -/
structure StatisticsMessage where
  sequenceNumber : BitVec 32
  securityCode : BitVec 32
  transactionDateAndTime : BitVec 64
  dataCount : BitVec 8
  dataCode : Alpha 1
  deriving DecidableEq, Repr

namespace StatisticsMessage

def encode (message : StatisticsMessage) : List UInt8 :=
  encodeUIntLE 4 message.sequenceNumber
    ++ (encodeUIntLE 4 message.securityCode
    ++ (encodeUIntLE 8 message.transactionDateAndTime
    ++ (encodeUIntLE 1 message.dataCount
    ++ (Alpha.encode message.dataCode))))

def decode (bytes : List UInt8) : Option (StatisticsMessage × List UInt8) := do
  let (sequenceNumber, bytes) ← decodeUIntLE 4 bytes
  let (securityCode, bytes) ← decodeUIntLE 4 bytes
  let (transactionDateAndTime, bytes) ← decodeUIntLE 8 bytes
  let (dataCount, bytes) ← decodeUIntLE 1 bytes
  let (dataCode, bytes) ← Alpha.decode 1 bytes
  pure ({ sequenceNumber, securityCode, transactionDateAndTime, dataCount, dataCode }, bytes)

@[simp] theorem encode_length (message : StatisticsMessage) : (encode message).length = 18 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : StatisticsMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : StatisticsMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end StatisticsMessage

/-- Security List Message: 976 bytes -/
structure SecurityListMessage where
  sequenceNumber : BitVec 32
  marketId : Alpha 4
  marketSegmentId : Alpha 4
  securityCode : BitVec 32
  symbol : Alpha 22
  symbolIsin : Alpha 12
  fisn : Alpha 35
  issuerLei : Alpha 20
  securityGroup : Alpha 2
  cfiCode : Alpha 6
  securityType : Alpha 2
  maturityDate : BitVec 32
  issueDate : BitVec 32
  contractMultiplier : BitVec 64
  liSpre : BitVec 64
  sstIpre : BitVec 64
  liSpost : BitVec 64
  sstIpost : BitVec 64
  liquidInstrument : BitVec 8
  admissionRequestedByIssuer : BitVec 8
  minTradeVol : BitVec 32
  roundLot : BitVec 32
  currency : Alpha 3
  modalityMaskB4 : BitVec 32
  securityDescription : Alpha 80
  tradingObligation : BitVec 8
  securityName : Alpha 40
  netAssetValueIdentifier : Alpha 7
  securitySubType : Alpha 2
  maturityMonthYear : Alpha 8
  securityStatus : SecurityStatus
  strikePrice : BitVec 64
  strikeValue : BitVec 64
  exerciseStyle : ExerciseStyle
  putOrCall : PutOrCall
  positionLimit : BitVec 64
  ntPositionLimit : BitVec 64
  issuer : Alpha 12
  cpRegType : BitVec 8
  barrier : BitVec 64
  lastTradingDay : BitVec 32
  automaticExpiration : BitVec 8
  feeType : Alpha 2
  barrier2 : BitVec 64
  triggerBarrier : BitVec 64
  triggerUpperBarrier : BitVec 64
  averageQuarterlyTurnover : BitVec 64
  tradingScope : BitVec 8
  sicavCounterpartyMember : Alpha 4
  netAssetValueIndicator : BitVec 8
  referenceTradingVenue : ReferenceTradingVenue
  outstandingCapital : BitVec 64
  firstTradingDate : BitVec 32
  settlementSystem : SettlementSystem
  numberOfDecimals : BitVec 8
  numberOfHolders : BitVec 32
  outstandingShares : BitVec 32
  minimumAuthorizedShares : BitVec 32
  minimumCapital : BitVec 64
  lastAdmissionDate : BitVec 32
  barrierReturn : BitVec 64
  investmentFundManager : Alpha 80
  effectiveAmountFiltersRoutedOrders : BitVec 64
  orderNumberOfDecimals : BitVec 8
  investmentFundClass : BitVec 8
  masterFundName : Alpha 80
  investmentFundManagementCompany : Alpha 80
  investmentFundDepository : Alpha 80
  investmentFundCategory : Alpha 80
  investmentFundMinimumSubscriptionAmount : BitVec 64
  investmentFundMinimumMaintenanceAmount : BitVec 64
  investmentFundCutOffTime : BitVec 64
  navCommunicationTerm : NavCommunicationTerm
  investmentFundNumberOfDecimals : BitVec 8
  commodityDerivativeIndicator : CommodityDerivativeIndicator
  doubleVolumeCapReached : BitVec 8
  adt : BitVec 64
  baseProduct : Alpha 4
  subProduct : Alpha 4
  furtherSubProduct : Alpha 4
  adnt : BitVec 64
  priceTickRule : BitVec 8
  underlyingSymbol : Alpha 22
  underlyingIsin : Alpha 12
  underlyingCurrency : Alpha 3
  minimumDisplayQty : BitVec 32
  retailServiceFlag : BitVec 8
  selfMatchPrevention : BitVec 8
  deriving DecidableEq, Repr

namespace SecurityListMessage

def encode (message : SecurityListMessage) : List UInt8 :=
  encodeUIntLE 4 message.sequenceNumber
    ++ (Alpha.encode message.marketId
    ++ (Alpha.encode message.marketSegmentId
    ++ (encodeUIntLE 4 message.securityCode
    ++ (Alpha.encode message.symbol
    ++ (Alpha.encode message.symbolIsin
    ++ (Alpha.encode message.fisn
    ++ (Alpha.encode message.issuerLei
    ++ (Alpha.encode message.securityGroup
    ++ (Alpha.encode message.cfiCode
    ++ (Alpha.encode message.securityType
    ++ (encodeUIntLE 4 message.maturityDate
    ++ (encodeUIntLE 4 message.issueDate
    ++ (encodeUIntLE 8 message.contractMultiplier
    ++ (encodeUIntLE 8 message.liSpre
    ++ (encodeUIntLE 8 message.sstIpre
    ++ (encodeUIntLE 8 message.liSpost
    ++ (encodeUIntLE 8 message.sstIpost
    ++ (encodeUIntLE 1 message.liquidInstrument
    ++ (encodeUIntLE 1 message.admissionRequestedByIssuer
    ++ (encodeUIntLE 4 message.minTradeVol
    ++ (encodeUIntLE 4 message.roundLot
    ++ (Alpha.encode message.currency
    ++ (encodeUIntLE 4 message.modalityMaskB4
    ++ (Alpha.encode message.securityDescription
    ++ (encodeUIntLE 1 message.tradingObligation
    ++ (Alpha.encode message.securityName
    ++ (Alpha.encode message.netAssetValueIdentifier
    ++ (Alpha.encode message.securitySubType
    ++ (Alpha.encode message.maturityMonthYear
    ++ (SecurityStatus.encode message.securityStatus
    ++ (encodeUIntLE 8 message.strikePrice
    ++ (encodeUIntLE 8 message.strikeValue
    ++ (ExerciseStyle.encode message.exerciseStyle
    ++ (PutOrCall.encode message.putOrCall
    ++ (encodeUIntLE 8 message.positionLimit
    ++ (encodeUIntLE 8 message.ntPositionLimit
    ++ (Alpha.encode message.issuer
    ++ (encodeUIntLE 1 message.cpRegType
    ++ (encodeUIntLE 8 message.barrier
    ++ (encodeUIntLE 4 message.lastTradingDay
    ++ (encodeUIntLE 1 message.automaticExpiration
    ++ (Alpha.encode message.feeType
    ++ (encodeUIntLE 8 message.barrier2
    ++ (encodeUIntLE 8 message.triggerBarrier
    ++ (encodeUIntLE 8 message.triggerUpperBarrier
    ++ (encodeUIntLE 8 message.averageQuarterlyTurnover
    ++ (encodeUIntLE 1 message.tradingScope
    ++ (Alpha.encode message.sicavCounterpartyMember
    ++ (encodeUIntLE 1 message.netAssetValueIndicator
    ++ (ReferenceTradingVenue.encode message.referenceTradingVenue
    ++ (encodeUIntLE 8 message.outstandingCapital
    ++ (encodeUIntLE 4 message.firstTradingDate
    ++ (SettlementSystem.encode message.settlementSystem
    ++ (encodeUIntLE 1 message.numberOfDecimals
    ++ (encodeUIntLE 4 message.numberOfHolders
    ++ (encodeUIntLE 4 message.outstandingShares
    ++ (encodeUIntLE 4 message.minimumAuthorizedShares
    ++ (encodeUIntLE 8 message.minimumCapital
    ++ (encodeUIntLE 4 message.lastAdmissionDate
    ++ (encodeUIntLE 8 message.barrierReturn
    ++ (Alpha.encode message.investmentFundManager
    ++ (encodeUIntLE 8 message.effectiveAmountFiltersRoutedOrders
    ++ (encodeUIntLE 1 message.orderNumberOfDecimals
    ++ (encodeUIntLE 1 message.investmentFundClass
    ++ (Alpha.encode message.masterFundName
    ++ (Alpha.encode message.investmentFundManagementCompany
    ++ (Alpha.encode message.investmentFundDepository
    ++ (Alpha.encode message.investmentFundCategory
    ++ (encodeUIntLE 8 message.investmentFundMinimumSubscriptionAmount
    ++ (encodeUIntLE 8 message.investmentFundMinimumMaintenanceAmount
    ++ (encodeUIntLE 8 message.investmentFundCutOffTime
    ++ (NavCommunicationTerm.encode message.navCommunicationTerm
    ++ (encodeUIntLE 1 message.investmentFundNumberOfDecimals
    ++ (CommodityDerivativeIndicator.encode message.commodityDerivativeIndicator
    ++ (encodeUIntLE 1 message.doubleVolumeCapReached
    ++ (encodeUIntLE 8 message.adt
    ++ (Alpha.encode message.baseProduct
    ++ (Alpha.encode message.subProduct
    ++ (Alpha.encode message.furtherSubProduct
    ++ (encodeUIntLE 8 message.adnt
    ++ (encodeUIntLE 1 message.priceTickRule
    ++ (Alpha.encode message.underlyingSymbol
    ++ (Alpha.encode message.underlyingIsin
    ++ (Alpha.encode message.underlyingCurrency
    ++ (encodeUIntLE 4 message.minimumDisplayQty
    ++ (encodeUIntLE 1 message.retailServiceFlag
    ++ (encodeUIntLE 1 message.selfMatchPrevention)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (SecurityListMessage × List UInt8) := do
  let (sequenceNumber, bytes) ← decodeUIntLE 4 bytes
  let (marketId, bytes) ← Alpha.decode 4 bytes
  let (marketSegmentId, bytes) ← Alpha.decode 4 bytes
  let (securityCode, bytes) ← decodeUIntLE 4 bytes
  let (symbol, bytes) ← Alpha.decode 22 bytes
  let (symbolIsin, bytes) ← Alpha.decode 12 bytes
  let (fisn, bytes) ← Alpha.decode 35 bytes
  let (issuerLei, bytes) ← Alpha.decode 20 bytes
  let (securityGroup, bytes) ← Alpha.decode 2 bytes
  let (cfiCode, bytes) ← Alpha.decode 6 bytes
  let (securityType, bytes) ← Alpha.decode 2 bytes
  let (maturityDate, bytes) ← decodeUIntLE 4 bytes
  let (issueDate, bytes) ← decodeUIntLE 4 bytes
  let (contractMultiplier, bytes) ← decodeUIntLE 8 bytes
  let (liSpre, bytes) ← decodeUIntLE 8 bytes
  let (sstIpre, bytes) ← decodeUIntLE 8 bytes
  let (liSpost, bytes) ← decodeUIntLE 8 bytes
  let (sstIpost, bytes) ← decodeUIntLE 8 bytes
  let (liquidInstrument, bytes) ← decodeUIntLE 1 bytes
  let (admissionRequestedByIssuer, bytes) ← decodeUIntLE 1 bytes
  let (minTradeVol, bytes) ← decodeUIntLE 4 bytes
  let (roundLot, bytes) ← decodeUIntLE 4 bytes
  let (currency, bytes) ← Alpha.decode 3 bytes
  let (modalityMaskB4, bytes) ← decodeUIntLE 4 bytes
  let (securityDescription, bytes) ← Alpha.decode 80 bytes
  let (tradingObligation, bytes) ← decodeUIntLE 1 bytes
  let (securityName, bytes) ← Alpha.decode 40 bytes
  let (netAssetValueIdentifier, bytes) ← Alpha.decode 7 bytes
  let (securitySubType, bytes) ← Alpha.decode 2 bytes
  let (maturityMonthYear, bytes) ← Alpha.decode 8 bytes
  let (securityStatus, bytes) ← SecurityStatus.decode bytes
  let (strikePrice, bytes) ← decodeUIntLE 8 bytes
  let (strikeValue, bytes) ← decodeUIntLE 8 bytes
  let (exerciseStyle, bytes) ← ExerciseStyle.decode bytes
  let (putOrCall, bytes) ← PutOrCall.decode bytes
  let (positionLimit, bytes) ← decodeUIntLE 8 bytes
  let (ntPositionLimit, bytes) ← decodeUIntLE 8 bytes
  let (issuer, bytes) ← Alpha.decode 12 bytes
  let (cpRegType, bytes) ← decodeUIntLE 1 bytes
  let (barrier, bytes) ← decodeUIntLE 8 bytes
  let (lastTradingDay, bytes) ← decodeUIntLE 4 bytes
  let (automaticExpiration, bytes) ← decodeUIntLE 1 bytes
  let (feeType, bytes) ← Alpha.decode 2 bytes
  let (barrier2, bytes) ← decodeUIntLE 8 bytes
  let (triggerBarrier, bytes) ← decodeUIntLE 8 bytes
  let (triggerUpperBarrier, bytes) ← decodeUIntLE 8 bytes
  let (averageQuarterlyTurnover, bytes) ← decodeUIntLE 8 bytes
  let (tradingScope, bytes) ← decodeUIntLE 1 bytes
  let (sicavCounterpartyMember, bytes) ← Alpha.decode 4 bytes
  let (netAssetValueIndicator, bytes) ← decodeUIntLE 1 bytes
  let (referenceTradingVenue, bytes) ← ReferenceTradingVenue.decode bytes
  let (outstandingCapital, bytes) ← decodeUIntLE 8 bytes
  let (firstTradingDate, bytes) ← decodeUIntLE 4 bytes
  let (settlementSystem, bytes) ← SettlementSystem.decode bytes
  let (numberOfDecimals, bytes) ← decodeUIntLE 1 bytes
  let (numberOfHolders, bytes) ← decodeUIntLE 4 bytes
  let (outstandingShares, bytes) ← decodeUIntLE 4 bytes
  let (minimumAuthorizedShares, bytes) ← decodeUIntLE 4 bytes
  let (minimumCapital, bytes) ← decodeUIntLE 8 bytes
  let (lastAdmissionDate, bytes) ← decodeUIntLE 4 bytes
  let (barrierReturn, bytes) ← decodeUIntLE 8 bytes
  let (investmentFundManager, bytes) ← Alpha.decode 80 bytes
  let (effectiveAmountFiltersRoutedOrders, bytes) ← decodeUIntLE 8 bytes
  let (orderNumberOfDecimals, bytes) ← decodeUIntLE 1 bytes
  let (investmentFundClass, bytes) ← decodeUIntLE 1 bytes
  let (masterFundName, bytes) ← Alpha.decode 80 bytes
  let (investmentFundManagementCompany, bytes) ← Alpha.decode 80 bytes
  let (investmentFundDepository, bytes) ← Alpha.decode 80 bytes
  let (investmentFundCategory, bytes) ← Alpha.decode 80 bytes
  let (investmentFundMinimumSubscriptionAmount, bytes) ← decodeUIntLE 8 bytes
  let (investmentFundMinimumMaintenanceAmount, bytes) ← decodeUIntLE 8 bytes
  let (investmentFundCutOffTime, bytes) ← decodeUIntLE 8 bytes
  let (navCommunicationTerm, bytes) ← NavCommunicationTerm.decode bytes
  let (investmentFundNumberOfDecimals, bytes) ← decodeUIntLE 1 bytes
  let (commodityDerivativeIndicator, bytes) ← CommodityDerivativeIndicator.decode bytes
  let (doubleVolumeCapReached, bytes) ← decodeUIntLE 1 bytes
  let (adt, bytes) ← decodeUIntLE 8 bytes
  let (baseProduct, bytes) ← Alpha.decode 4 bytes
  let (subProduct, bytes) ← Alpha.decode 4 bytes
  let (furtherSubProduct, bytes) ← Alpha.decode 4 bytes
  let (adnt, bytes) ← decodeUIntLE 8 bytes
  let (priceTickRule, bytes) ← decodeUIntLE 1 bytes
  let (underlyingSymbol, bytes) ← Alpha.decode 22 bytes
  let (underlyingIsin, bytes) ← Alpha.decode 12 bytes
  let (underlyingCurrency, bytes) ← Alpha.decode 3 bytes
  let (minimumDisplayQty, bytes) ← decodeUIntLE 4 bytes
  let (retailServiceFlag, bytes) ← decodeUIntLE 1 bytes
  let (selfMatchPrevention, bytes) ← decodeUIntLE 1 bytes
  pure ({ sequenceNumber, marketId, marketSegmentId, securityCode, symbol, symbolIsin, fisn, issuerLei, securityGroup, cfiCode, securityType, maturityDate, issueDate, contractMultiplier, liSpre, sstIpre, liSpost, sstIpost, liquidInstrument, admissionRequestedByIssuer, minTradeVol, roundLot, currency, modalityMaskB4, securityDescription, tradingObligation, securityName, netAssetValueIdentifier, securitySubType, maturityMonthYear, securityStatus, strikePrice, strikeValue, exerciseStyle, putOrCall, positionLimit, ntPositionLimit, issuer, cpRegType, barrier, lastTradingDay, automaticExpiration, feeType, barrier2, triggerBarrier, triggerUpperBarrier, averageQuarterlyTurnover, tradingScope, sicavCounterpartyMember, netAssetValueIndicator, referenceTradingVenue, outstandingCapital, firstTradingDate, settlementSystem, numberOfDecimals, numberOfHolders, outstandingShares, minimumAuthorizedShares, minimumCapital, lastAdmissionDate, barrierReturn, investmentFundManager, effectiveAmountFiltersRoutedOrders, orderNumberOfDecimals, investmentFundClass, masterFundName, investmentFundManagementCompany, investmentFundDepository, investmentFundCategory, investmentFundMinimumSubscriptionAmount, investmentFundMinimumMaintenanceAmount, investmentFundCutOffTime, navCommunicationTerm, investmentFundNumberOfDecimals, commodityDerivativeIndicator, doubleVolumeCapReached, adt, baseProduct, subProduct, furtherSubProduct, adnt, priceTickRule, underlyingSymbol, underlyingIsin, underlyingCurrency, minimumDisplayQty, retailServiceFlag, selfMatchPrevention }, bytes)

@[simp] theorem encode_length (message : SecurityListMessage) : (encode message).length = 976 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, SecurityStatus.encode_length, ExerciseStyle.encode_length, PutOrCall.encode_length, ReferenceTradingVenue.encode_length, SettlementSystem.encode_length, NavCommunicationTerm.encode_length, CommodityDerivativeIndicator.encode_length]

theorem encode_length_pos (message : SecurityListMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : SecurityListMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SecurityStatus.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, ExerciseStyle.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, PutOrCall.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, ReferenceTradingVenue.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, SettlementSystem.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, NavCommunicationTerm.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, CommodityDerivativeIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end SecurityListMessage

/-- Security List Update Report Message: 976 bytes -/
structure SecurityListUpdateReportMessage where
  sequenceNumber : BitVec 32
  marketId : Alpha 4
  marketSegmentId : Alpha 4
  securityCode : BitVec 32
  symbol : Alpha 22
  symbolIsin : Alpha 12
  fisn : Alpha 35
  issuerLei : Alpha 20
  securityGroup : Alpha 2
  cfiCode : Alpha 6
  securityType : Alpha 2
  maturityDate : BitVec 32
  issueDate : BitVec 32
  contractMultiplier : BitVec 64
  liSpre : BitVec 64
  sstIpre : BitVec 64
  liSpost : BitVec 64
  sstIpost : BitVec 64
  liquidInstrument : BitVec 8
  admissionRequestedByIssuer : BitVec 8
  minTradeVol : BitVec 32
  roundLot : BitVec 32
  currency : Alpha 3
  modalityMaskB4 : BitVec 32
  securityDescription : Alpha 80
  tradingObligation : BitVec 8
  securityName : Alpha 40
  netAssetValueIdentifier : Alpha 7
  securitySubType : Alpha 2
  maturityMonthYear : Alpha 8
  securityStatus : SecurityStatus
  strikePrice : BitVec 64
  strikeValue : BitVec 64
  exerciseStyle : ExerciseStyle
  putOrCall : PutOrCall
  positionLimit : BitVec 64
  ntPositionLimit : BitVec 64
  issuer : Alpha 12
  cpRegType : BitVec 8
  barrier : BitVec 64
  lastTradingDay : BitVec 32
  automaticExpiration : BitVec 8
  feeType : Alpha 2
  barrier2 : BitVec 64
  triggerBarrier : BitVec 64
  triggerUpperBarrier : BitVec 64
  averageQuarterlyTurnover : BitVec 64
  tradingScope : BitVec 8
  sicavCounterpartyMember : Alpha 4
  netAssetValueIndicator : BitVec 8
  referenceTradingVenue : ReferenceTradingVenue
  outstandingCapital : BitVec 64
  firstTradingDate : BitVec 32
  settlementSystem : SettlementSystem
  numberOfDecimals : BitVec 8
  numberOfHolders : BitVec 32
  outstandingShares : BitVec 32
  minimumAuthorizedShares : BitVec 32
  minimumCapital : BitVec 64
  lastAdmissionDate : BitVec 32
  barrierReturn : BitVec 64
  investmentFundManager : Alpha 80
  effectiveAmountFiltersRoutedOrders : BitVec 64
  orderNumberOfDecimals : BitVec 8
  investmentFundClass : BitVec 8
  masterFundName : Alpha 80
  investmentFundManagementCompany : Alpha 80
  investmentFundDepository : Alpha 80
  investmentFundCategory : Alpha 80
  investmentFundMinimumSubscriptionAmount : BitVec 64
  investmentFundMinimumMaintenanceAmount : BitVec 64
  investmentFundCutOffTime : BitVec 64
  navCommunicationTerm : NavCommunicationTerm
  investmentFundNumberOfDecimals : BitVec 8
  commodityDerivativeIndicator : CommodityDerivativeIndicator
  doubleVolumeCapReached : BitVec 8
  adt : BitVec 64
  baseProduct : Alpha 4
  subProduct : Alpha 4
  furtherSubProduct : Alpha 4
  adnt : BitVec 64
  priceTickRule : BitVec 8
  underlyingSymbol : Alpha 22
  underlyingIsin : Alpha 12
  underlyingCurrency : Alpha 3
  minimumDisplayQty : BitVec 32
  retailServiceFlag : BitVec 8
  selfMatchPrevention : BitVec 8
  deriving DecidableEq, Repr

namespace SecurityListUpdateReportMessage

def encode (message : SecurityListUpdateReportMessage) : List UInt8 :=
  encodeUIntLE 4 message.sequenceNumber
    ++ (Alpha.encode message.marketId
    ++ (Alpha.encode message.marketSegmentId
    ++ (encodeUIntLE 4 message.securityCode
    ++ (Alpha.encode message.symbol
    ++ (Alpha.encode message.symbolIsin
    ++ (Alpha.encode message.fisn
    ++ (Alpha.encode message.issuerLei
    ++ (Alpha.encode message.securityGroup
    ++ (Alpha.encode message.cfiCode
    ++ (Alpha.encode message.securityType
    ++ (encodeUIntLE 4 message.maturityDate
    ++ (encodeUIntLE 4 message.issueDate
    ++ (encodeUIntLE 8 message.contractMultiplier
    ++ (encodeUIntLE 8 message.liSpre
    ++ (encodeUIntLE 8 message.sstIpre
    ++ (encodeUIntLE 8 message.liSpost
    ++ (encodeUIntLE 8 message.sstIpost
    ++ (encodeUIntLE 1 message.liquidInstrument
    ++ (encodeUIntLE 1 message.admissionRequestedByIssuer
    ++ (encodeUIntLE 4 message.minTradeVol
    ++ (encodeUIntLE 4 message.roundLot
    ++ (Alpha.encode message.currency
    ++ (encodeUIntLE 4 message.modalityMaskB4
    ++ (Alpha.encode message.securityDescription
    ++ (encodeUIntLE 1 message.tradingObligation
    ++ (Alpha.encode message.securityName
    ++ (Alpha.encode message.netAssetValueIdentifier
    ++ (Alpha.encode message.securitySubType
    ++ (Alpha.encode message.maturityMonthYear
    ++ (SecurityStatus.encode message.securityStatus
    ++ (encodeUIntLE 8 message.strikePrice
    ++ (encodeUIntLE 8 message.strikeValue
    ++ (ExerciseStyle.encode message.exerciseStyle
    ++ (PutOrCall.encode message.putOrCall
    ++ (encodeUIntLE 8 message.positionLimit
    ++ (encodeUIntLE 8 message.ntPositionLimit
    ++ (Alpha.encode message.issuer
    ++ (encodeUIntLE 1 message.cpRegType
    ++ (encodeUIntLE 8 message.barrier
    ++ (encodeUIntLE 4 message.lastTradingDay
    ++ (encodeUIntLE 1 message.automaticExpiration
    ++ (Alpha.encode message.feeType
    ++ (encodeUIntLE 8 message.barrier2
    ++ (encodeUIntLE 8 message.triggerBarrier
    ++ (encodeUIntLE 8 message.triggerUpperBarrier
    ++ (encodeUIntLE 8 message.averageQuarterlyTurnover
    ++ (encodeUIntLE 1 message.tradingScope
    ++ (Alpha.encode message.sicavCounterpartyMember
    ++ (encodeUIntLE 1 message.netAssetValueIndicator
    ++ (ReferenceTradingVenue.encode message.referenceTradingVenue
    ++ (encodeUIntLE 8 message.outstandingCapital
    ++ (encodeUIntLE 4 message.firstTradingDate
    ++ (SettlementSystem.encode message.settlementSystem
    ++ (encodeUIntLE 1 message.numberOfDecimals
    ++ (encodeUIntLE 4 message.numberOfHolders
    ++ (encodeUIntLE 4 message.outstandingShares
    ++ (encodeUIntLE 4 message.minimumAuthorizedShares
    ++ (encodeUIntLE 8 message.minimumCapital
    ++ (encodeUIntLE 4 message.lastAdmissionDate
    ++ (encodeUIntLE 8 message.barrierReturn
    ++ (Alpha.encode message.investmentFundManager
    ++ (encodeUIntLE 8 message.effectiveAmountFiltersRoutedOrders
    ++ (encodeUIntLE 1 message.orderNumberOfDecimals
    ++ (encodeUIntLE 1 message.investmentFundClass
    ++ (Alpha.encode message.masterFundName
    ++ (Alpha.encode message.investmentFundManagementCompany
    ++ (Alpha.encode message.investmentFundDepository
    ++ (Alpha.encode message.investmentFundCategory
    ++ (encodeUIntLE 8 message.investmentFundMinimumSubscriptionAmount
    ++ (encodeUIntLE 8 message.investmentFundMinimumMaintenanceAmount
    ++ (encodeUIntLE 8 message.investmentFundCutOffTime
    ++ (NavCommunicationTerm.encode message.navCommunicationTerm
    ++ (encodeUIntLE 1 message.investmentFundNumberOfDecimals
    ++ (CommodityDerivativeIndicator.encode message.commodityDerivativeIndicator
    ++ (encodeUIntLE 1 message.doubleVolumeCapReached
    ++ (encodeUIntLE 8 message.adt
    ++ (Alpha.encode message.baseProduct
    ++ (Alpha.encode message.subProduct
    ++ (Alpha.encode message.furtherSubProduct
    ++ (encodeUIntLE 8 message.adnt
    ++ (encodeUIntLE 1 message.priceTickRule
    ++ (Alpha.encode message.underlyingSymbol
    ++ (Alpha.encode message.underlyingIsin
    ++ (Alpha.encode message.underlyingCurrency
    ++ (encodeUIntLE 4 message.minimumDisplayQty
    ++ (encodeUIntLE 1 message.retailServiceFlag
    ++ (encodeUIntLE 1 message.selfMatchPrevention)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (SecurityListUpdateReportMessage × List UInt8) := do
  let (sequenceNumber, bytes) ← decodeUIntLE 4 bytes
  let (marketId, bytes) ← Alpha.decode 4 bytes
  let (marketSegmentId, bytes) ← Alpha.decode 4 bytes
  let (securityCode, bytes) ← decodeUIntLE 4 bytes
  let (symbol, bytes) ← Alpha.decode 22 bytes
  let (symbolIsin, bytes) ← Alpha.decode 12 bytes
  let (fisn, bytes) ← Alpha.decode 35 bytes
  let (issuerLei, bytes) ← Alpha.decode 20 bytes
  let (securityGroup, bytes) ← Alpha.decode 2 bytes
  let (cfiCode, bytes) ← Alpha.decode 6 bytes
  let (securityType, bytes) ← Alpha.decode 2 bytes
  let (maturityDate, bytes) ← decodeUIntLE 4 bytes
  let (issueDate, bytes) ← decodeUIntLE 4 bytes
  let (contractMultiplier, bytes) ← decodeUIntLE 8 bytes
  let (liSpre, bytes) ← decodeUIntLE 8 bytes
  let (sstIpre, bytes) ← decodeUIntLE 8 bytes
  let (liSpost, bytes) ← decodeUIntLE 8 bytes
  let (sstIpost, bytes) ← decodeUIntLE 8 bytes
  let (liquidInstrument, bytes) ← decodeUIntLE 1 bytes
  let (admissionRequestedByIssuer, bytes) ← decodeUIntLE 1 bytes
  let (minTradeVol, bytes) ← decodeUIntLE 4 bytes
  let (roundLot, bytes) ← decodeUIntLE 4 bytes
  let (currency, bytes) ← Alpha.decode 3 bytes
  let (modalityMaskB4, bytes) ← decodeUIntLE 4 bytes
  let (securityDescription, bytes) ← Alpha.decode 80 bytes
  let (tradingObligation, bytes) ← decodeUIntLE 1 bytes
  let (securityName, bytes) ← Alpha.decode 40 bytes
  let (netAssetValueIdentifier, bytes) ← Alpha.decode 7 bytes
  let (securitySubType, bytes) ← Alpha.decode 2 bytes
  let (maturityMonthYear, bytes) ← Alpha.decode 8 bytes
  let (securityStatus, bytes) ← SecurityStatus.decode bytes
  let (strikePrice, bytes) ← decodeUIntLE 8 bytes
  let (strikeValue, bytes) ← decodeUIntLE 8 bytes
  let (exerciseStyle, bytes) ← ExerciseStyle.decode bytes
  let (putOrCall, bytes) ← PutOrCall.decode bytes
  let (positionLimit, bytes) ← decodeUIntLE 8 bytes
  let (ntPositionLimit, bytes) ← decodeUIntLE 8 bytes
  let (issuer, bytes) ← Alpha.decode 12 bytes
  let (cpRegType, bytes) ← decodeUIntLE 1 bytes
  let (barrier, bytes) ← decodeUIntLE 8 bytes
  let (lastTradingDay, bytes) ← decodeUIntLE 4 bytes
  let (automaticExpiration, bytes) ← decodeUIntLE 1 bytes
  let (feeType, bytes) ← Alpha.decode 2 bytes
  let (barrier2, bytes) ← decodeUIntLE 8 bytes
  let (triggerBarrier, bytes) ← decodeUIntLE 8 bytes
  let (triggerUpperBarrier, bytes) ← decodeUIntLE 8 bytes
  let (averageQuarterlyTurnover, bytes) ← decodeUIntLE 8 bytes
  let (tradingScope, bytes) ← decodeUIntLE 1 bytes
  let (sicavCounterpartyMember, bytes) ← Alpha.decode 4 bytes
  let (netAssetValueIndicator, bytes) ← decodeUIntLE 1 bytes
  let (referenceTradingVenue, bytes) ← ReferenceTradingVenue.decode bytes
  let (outstandingCapital, bytes) ← decodeUIntLE 8 bytes
  let (firstTradingDate, bytes) ← decodeUIntLE 4 bytes
  let (settlementSystem, bytes) ← SettlementSystem.decode bytes
  let (numberOfDecimals, bytes) ← decodeUIntLE 1 bytes
  let (numberOfHolders, bytes) ← decodeUIntLE 4 bytes
  let (outstandingShares, bytes) ← decodeUIntLE 4 bytes
  let (minimumAuthorizedShares, bytes) ← decodeUIntLE 4 bytes
  let (minimumCapital, bytes) ← decodeUIntLE 8 bytes
  let (lastAdmissionDate, bytes) ← decodeUIntLE 4 bytes
  let (barrierReturn, bytes) ← decodeUIntLE 8 bytes
  let (investmentFundManager, bytes) ← Alpha.decode 80 bytes
  let (effectiveAmountFiltersRoutedOrders, bytes) ← decodeUIntLE 8 bytes
  let (orderNumberOfDecimals, bytes) ← decodeUIntLE 1 bytes
  let (investmentFundClass, bytes) ← decodeUIntLE 1 bytes
  let (masterFundName, bytes) ← Alpha.decode 80 bytes
  let (investmentFundManagementCompany, bytes) ← Alpha.decode 80 bytes
  let (investmentFundDepository, bytes) ← Alpha.decode 80 bytes
  let (investmentFundCategory, bytes) ← Alpha.decode 80 bytes
  let (investmentFundMinimumSubscriptionAmount, bytes) ← decodeUIntLE 8 bytes
  let (investmentFundMinimumMaintenanceAmount, bytes) ← decodeUIntLE 8 bytes
  let (investmentFundCutOffTime, bytes) ← decodeUIntLE 8 bytes
  let (navCommunicationTerm, bytes) ← NavCommunicationTerm.decode bytes
  let (investmentFundNumberOfDecimals, bytes) ← decodeUIntLE 1 bytes
  let (commodityDerivativeIndicator, bytes) ← CommodityDerivativeIndicator.decode bytes
  let (doubleVolumeCapReached, bytes) ← decodeUIntLE 1 bytes
  let (adt, bytes) ← decodeUIntLE 8 bytes
  let (baseProduct, bytes) ← Alpha.decode 4 bytes
  let (subProduct, bytes) ← Alpha.decode 4 bytes
  let (furtherSubProduct, bytes) ← Alpha.decode 4 bytes
  let (adnt, bytes) ← decodeUIntLE 8 bytes
  let (priceTickRule, bytes) ← decodeUIntLE 1 bytes
  let (underlyingSymbol, bytes) ← Alpha.decode 22 bytes
  let (underlyingIsin, bytes) ← Alpha.decode 12 bytes
  let (underlyingCurrency, bytes) ← Alpha.decode 3 bytes
  let (minimumDisplayQty, bytes) ← decodeUIntLE 4 bytes
  let (retailServiceFlag, bytes) ← decodeUIntLE 1 bytes
  let (selfMatchPrevention, bytes) ← decodeUIntLE 1 bytes
  pure ({ sequenceNumber, marketId, marketSegmentId, securityCode, symbol, symbolIsin, fisn, issuerLei, securityGroup, cfiCode, securityType, maturityDate, issueDate, contractMultiplier, liSpre, sstIpre, liSpost, sstIpost, liquidInstrument, admissionRequestedByIssuer, minTradeVol, roundLot, currency, modalityMaskB4, securityDescription, tradingObligation, securityName, netAssetValueIdentifier, securitySubType, maturityMonthYear, securityStatus, strikePrice, strikeValue, exerciseStyle, putOrCall, positionLimit, ntPositionLimit, issuer, cpRegType, barrier, lastTradingDay, automaticExpiration, feeType, barrier2, triggerBarrier, triggerUpperBarrier, averageQuarterlyTurnover, tradingScope, sicavCounterpartyMember, netAssetValueIndicator, referenceTradingVenue, outstandingCapital, firstTradingDate, settlementSystem, numberOfDecimals, numberOfHolders, outstandingShares, minimumAuthorizedShares, minimumCapital, lastAdmissionDate, barrierReturn, investmentFundManager, effectiveAmountFiltersRoutedOrders, orderNumberOfDecimals, investmentFundClass, masterFundName, investmentFundManagementCompany, investmentFundDepository, investmentFundCategory, investmentFundMinimumSubscriptionAmount, investmentFundMinimumMaintenanceAmount, investmentFundCutOffTime, navCommunicationTerm, investmentFundNumberOfDecimals, commodityDerivativeIndicator, doubleVolumeCapReached, adt, baseProduct, subProduct, furtherSubProduct, adnt, priceTickRule, underlyingSymbol, underlyingIsin, underlyingCurrency, minimumDisplayQty, retailServiceFlag, selfMatchPrevention }, bytes)

@[simp] theorem encode_length (message : SecurityListUpdateReportMessage) : (encode message).length = 976 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, SecurityStatus.encode_length, ExerciseStyle.encode_length, PutOrCall.encode_length, ReferenceTradingVenue.encode_length, SettlementSystem.encode_length, NavCommunicationTerm.encode_length, CommodityDerivativeIndicator.encode_length]

theorem encode_length_pos (message : SecurityListUpdateReportMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : SecurityListUpdateReportMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SecurityStatus.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, ExerciseStyle.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, PutOrCall.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, ReferenceTradingVenue.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, SettlementSystem.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, NavCommunicationTerm.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, CommodityDerivativeIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end SecurityListUpdateReportMessage

/-- Security Status Message: 115 bytes -/
structure SecurityStatusMessage where
  sequenceNumber : BitVec 32
  securityCode : BitVec 32
  transactionDateAndTime : BitVec 64
  referencePrice : BitVec 64
  staticPrice : BitVec 64
  dynamicPriceOscilationPercentage : BitVec 64
  dynamicRangeMultiplier : BitVec 8
  auctionTriggerPrice : BitVec 64
  auctionEndTime : BitVec 64
  liquidativeValueDate : BitVec 32
  bonusWarrantsWithActiveBonus : BitVec 8
  securityTradingStatus : BitVec 8
  auctionOrigin : BitVec 8
  nonAvailabilityReason : BitVec 8
  exemptionSituation : ExemptionSituation
  blockOscilationPercentage : BitVec 64
  highLimitPrice : BitVec 64
  lowLimitPrice : BitVec 64
  liquidativeValue : BitVec 64
  staticRangeType : StaticRangeType
  orderStaticRange : BitVec 64
  blockStaticRange : BitVec 64
  deriving DecidableEq, Repr

namespace SecurityStatusMessage

def encode (message : SecurityStatusMessage) : List UInt8 :=
  encodeUIntLE 4 message.sequenceNumber
    ++ (encodeUIntLE 4 message.securityCode
    ++ (encodeUIntLE 8 message.transactionDateAndTime
    ++ (encodeUIntLE 8 message.referencePrice
    ++ (encodeUIntLE 8 message.staticPrice
    ++ (encodeUIntLE 8 message.dynamicPriceOscilationPercentage
    ++ (encodeUIntLE 1 message.dynamicRangeMultiplier
    ++ (encodeUIntLE 8 message.auctionTriggerPrice
    ++ (encodeUIntLE 8 message.auctionEndTime
    ++ (encodeUIntLE 4 message.liquidativeValueDate
    ++ (encodeUIntLE 1 message.bonusWarrantsWithActiveBonus
    ++ (encodeUIntLE 1 message.securityTradingStatus
    ++ (encodeUIntLE 1 message.auctionOrigin
    ++ (encodeUIntLE 1 message.nonAvailabilityReason
    ++ (ExemptionSituation.encode message.exemptionSituation
    ++ (encodeUIntLE 8 message.blockOscilationPercentage
    ++ (encodeUIntLE 8 message.highLimitPrice
    ++ (encodeUIntLE 8 message.lowLimitPrice
    ++ (encodeUIntLE 8 message.liquidativeValue
    ++ (StaticRangeType.encode message.staticRangeType
    ++ (encodeUIntLE 8 message.orderStaticRange
    ++ (encodeUIntLE 8 message.blockStaticRange)))))))))))))))))))))

def decode (bytes : List UInt8) : Option (SecurityStatusMessage × List UInt8) := do
  let (sequenceNumber, bytes) ← decodeUIntLE 4 bytes
  let (securityCode, bytes) ← decodeUIntLE 4 bytes
  let (transactionDateAndTime, bytes) ← decodeUIntLE 8 bytes
  let (referencePrice, bytes) ← decodeUIntLE 8 bytes
  let (staticPrice, bytes) ← decodeUIntLE 8 bytes
  let (dynamicPriceOscilationPercentage, bytes) ← decodeUIntLE 8 bytes
  let (dynamicRangeMultiplier, bytes) ← decodeUIntLE 1 bytes
  let (auctionTriggerPrice, bytes) ← decodeUIntLE 8 bytes
  let (auctionEndTime, bytes) ← decodeUIntLE 8 bytes
  let (liquidativeValueDate, bytes) ← decodeUIntLE 4 bytes
  let (bonusWarrantsWithActiveBonus, bytes) ← decodeUIntLE 1 bytes
  let (securityTradingStatus, bytes) ← decodeUIntLE 1 bytes
  let (auctionOrigin, bytes) ← decodeUIntLE 1 bytes
  let (nonAvailabilityReason, bytes) ← decodeUIntLE 1 bytes
  let (exemptionSituation, bytes) ← ExemptionSituation.decode bytes
  let (blockOscilationPercentage, bytes) ← decodeUIntLE 8 bytes
  let (highLimitPrice, bytes) ← decodeUIntLE 8 bytes
  let (lowLimitPrice, bytes) ← decodeUIntLE 8 bytes
  let (liquidativeValue, bytes) ← decodeUIntLE 8 bytes
  let (staticRangeType, bytes) ← StaticRangeType.decode bytes
  let (orderStaticRange, bytes) ← decodeUIntLE 8 bytes
  let (blockStaticRange, bytes) ← decodeUIntLE 8 bytes
  pure ({ sequenceNumber, securityCode, transactionDateAndTime, referencePrice, staticPrice, dynamicPriceOscilationPercentage, dynamicRangeMultiplier, auctionTriggerPrice, auctionEndTime, liquidativeValueDate, bonusWarrantsWithActiveBonus, securityTradingStatus, auctionOrigin, nonAvailabilityReason, exemptionSituation, blockOscilationPercentage, highLimitPrice, lowLimitPrice, liquidativeValue, staticRangeType, orderStaticRange, blockStaticRange }, bytes)

@[simp] theorem encode_length (message : SecurityStatusMessage) : (encode message).length = 115 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, ExemptionSituation.encode_length, StaticRangeType.encode_length]

theorem encode_length_pos (message : SecurityStatusMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SecurityStatusMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, ExemptionSituation.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, StaticRangeType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end SecurityStatusMessage

/-- Order Book Clear Message: 16 bytes -/
structure OrderBookClearMessage where
  sequenceNumber : BitVec 32
  securityCode : BitVec 32
  transactionDateAndTime : BitVec 64
  deriving DecidableEq, Repr

namespace OrderBookClearMessage

def encode (message : OrderBookClearMessage) : List UInt8 :=
  encodeUIntLE 4 message.sequenceNumber
    ++ (encodeUIntLE 4 message.securityCode
    ++ (encodeUIntLE 8 message.transactionDateAndTime))

def decode (bytes : List UInt8) : Option (OrderBookClearMessage × List UInt8) := do
  let (sequenceNumber, bytes) ← decodeUIntLE 4 bytes
  let (securityCode, bytes) ← decodeUIntLE 4 bytes
  let (transactionDateAndTime, bytes) ← decodeUIntLE 8 bytes
  pure ({ sequenceNumber, securityCode, transactionDateAndTime }, bytes)

@[simp] theorem encode_length (message : OrderBookClearMessage) : (encode message).length = 16 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : OrderBookClearMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderBookClearMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end OrderBookClearMessage

/-- Order Market Pre Transparency Information Message: 42 bytes -/
structure OrderMarketPreTransparencyInformationMessage where
  sequenceNumber : BitVec 32
  securityCode : BitVec 32
  transactionDateAndTime : BitVec 64
  secondaryOrderId : BitVec 32
  entryDate : BitVec 32
  retailFlag : BitVec 8
  side : Side
  priority : BitVec 32
  price : BitVec 64
  displayQty : BitVec 32
  deriving DecidableEq, Repr

namespace OrderMarketPreTransparencyInformationMessage

def encode (message : OrderMarketPreTransparencyInformationMessage) : List UInt8 :=
  encodeUIntLE 4 message.sequenceNumber
    ++ (encodeUIntLE 4 message.securityCode
    ++ (encodeUIntLE 8 message.transactionDateAndTime
    ++ (encodeUIntLE 4 message.secondaryOrderId
    ++ (encodeUIntLE 4 message.entryDate
    ++ (encodeUIntLE 1 message.retailFlag
    ++ (Side.encode message.side
    ++ (encodeUIntLE 4 message.priority
    ++ (encodeUIntLE 8 message.price
    ++ (encodeUIntLE 4 message.displayQty)))))))))

def decode (bytes : List UInt8) : Option (OrderMarketPreTransparencyInformationMessage × List UInt8) := do
  let (sequenceNumber, bytes) ← decodeUIntLE 4 bytes
  let (securityCode, bytes) ← decodeUIntLE 4 bytes
  let (transactionDateAndTime, bytes) ← decodeUIntLE 8 bytes
  let (secondaryOrderId, bytes) ← decodeUIntLE 4 bytes
  let (entryDate, bytes) ← decodeUIntLE 4 bytes
  let (retailFlag, bytes) ← decodeUIntLE 1 bytes
  let (side, bytes) ← Side.decode bytes
  let (priority, bytes) ← decodeUIntLE 4 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (displayQty, bytes) ← decodeUIntLE 4 bytes
  pure ({ sequenceNumber, securityCode, transactionDateAndTime, secondaryOrderId, entryDate, retailFlag, side, priority, price, displayQty }, bytes)

@[simp] theorem encode_length (message : OrderMarketPreTransparencyInformationMessage) : (encode message).length = 42 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Side.encode_length]

theorem encode_length_pos (message : OrderMarketPreTransparencyInformationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderMarketPreTransparencyInformationMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Side.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end OrderMarketPreTransparencyInformationMessage

/-- Quote Market Pre Transparency Information Message: 57 bytes -/
structure QuoteMarketPreTransparencyInformationMessage where
  sequenceNumber : BitVec 32
  securityCode : BitVec 32
  transactionDateAndTime : BitVec 64
  secondaryOrderId : BitVec 32
  secondaryOrderId2 : BitVec 32
  retailFlag : BitVec 8
  priority : BitVec 32
  price : BitVec 64
  displayQty : BitVec 32
  priority2 : BitVec 32
  price2 : BitVec 64
  displayQty2 : BitVec 32
  deriving DecidableEq, Repr

namespace QuoteMarketPreTransparencyInformationMessage

def encode (message : QuoteMarketPreTransparencyInformationMessage) : List UInt8 :=
  encodeUIntLE 4 message.sequenceNumber
    ++ (encodeUIntLE 4 message.securityCode
    ++ (encodeUIntLE 8 message.transactionDateAndTime
    ++ (encodeUIntLE 4 message.secondaryOrderId
    ++ (encodeUIntLE 4 message.secondaryOrderId2
    ++ (encodeUIntLE 1 message.retailFlag
    ++ (encodeUIntLE 4 message.priority
    ++ (encodeUIntLE 8 message.price
    ++ (encodeUIntLE 4 message.displayQty
    ++ (encodeUIntLE 4 message.priority2
    ++ (encodeUIntLE 8 message.price2
    ++ (encodeUIntLE 4 message.displayQty2)))))))))))

def decode (bytes : List UInt8) : Option (QuoteMarketPreTransparencyInformationMessage × List UInt8) := do
  let (sequenceNumber, bytes) ← decodeUIntLE 4 bytes
  let (securityCode, bytes) ← decodeUIntLE 4 bytes
  let (transactionDateAndTime, bytes) ← decodeUIntLE 8 bytes
  let (secondaryOrderId, bytes) ← decodeUIntLE 4 bytes
  let (secondaryOrderId2, bytes) ← decodeUIntLE 4 bytes
  let (retailFlag, bytes) ← decodeUIntLE 1 bytes
  let (priority, bytes) ← decodeUIntLE 4 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (displayQty, bytes) ← decodeUIntLE 4 bytes
  let (priority2, bytes) ← decodeUIntLE 4 bytes
  let (price2, bytes) ← decodeUIntLE 8 bytes
  let (displayQty2, bytes) ← decodeUIntLE 4 bytes
  pure ({ sequenceNumber, securityCode, transactionDateAndTime, secondaryOrderId, secondaryOrderId2, retailFlag, priority, price, displayQty, priority2, price2, displayQty2 }, bytes)

@[simp] theorem encode_length (message : QuoteMarketPreTransparencyInformationMessage) : (encode message).length = 57 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : QuoteMarketPreTransparencyInformationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : QuoteMarketPreTransparencyInformationMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end QuoteMarketPreTransparencyInformationMessage

/-- Order Cancellation Market Member Message: 25 bytes -/
structure OrderCancellationMarketMemberMessage where
  sequenceNumber : BitVec 32
  securityCode : BitVec 32
  transactionDateAndTime : BitVec 64
  secondaryOrderId : BitVec 32
  entryDate : BitVec 32
  retailFlag : BitVec 8
  deriving DecidableEq, Repr

namespace OrderCancellationMarketMemberMessage

def encode (message : OrderCancellationMarketMemberMessage) : List UInt8 :=
  encodeUIntLE 4 message.sequenceNumber
    ++ (encodeUIntLE 4 message.securityCode
    ++ (encodeUIntLE 8 message.transactionDateAndTime
    ++ (encodeUIntLE 4 message.secondaryOrderId
    ++ (encodeUIntLE 4 message.entryDate
    ++ (encodeUIntLE 1 message.retailFlag)))))

def decode (bytes : List UInt8) : Option (OrderCancellationMarketMemberMessage × List UInt8) := do
  let (sequenceNumber, bytes) ← decodeUIntLE 4 bytes
  let (securityCode, bytes) ← decodeUIntLE 4 bytes
  let (transactionDateAndTime, bytes) ← decodeUIntLE 8 bytes
  let (secondaryOrderId, bytes) ← decodeUIntLE 4 bytes
  let (entryDate, bytes) ← decodeUIntLE 4 bytes
  let (retailFlag, bytes) ← decodeUIntLE 1 bytes
  pure ({ sequenceNumber, securityCode, transactionDateAndTime, secondaryOrderId, entryDate, retailFlag }, bytes)

@[simp] theorem encode_length (message : OrderCancellationMarketMemberMessage) : (encode message).length = 25 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : OrderCancellationMarketMemberMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderCancellationMarketMemberMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end OrderCancellationMarketMemberMessage

/-- Quote Cancellation Market Member Message: 25 bytes -/
structure QuoteCancellationMarketMemberMessage where
  sequenceNumber : BitVec 32
  securityCode : BitVec 32
  transactionDateAndTime : BitVec 64
  secondaryOrderId : BitVec 32
  secondaryOrderId2 : BitVec 32
  retailFlag : BitVec 8
  deriving DecidableEq, Repr

namespace QuoteCancellationMarketMemberMessage

def encode (message : QuoteCancellationMarketMemberMessage) : List UInt8 :=
  encodeUIntLE 4 message.sequenceNumber
    ++ (encodeUIntLE 4 message.securityCode
    ++ (encodeUIntLE 8 message.transactionDateAndTime
    ++ (encodeUIntLE 4 message.secondaryOrderId
    ++ (encodeUIntLE 4 message.secondaryOrderId2
    ++ (encodeUIntLE 1 message.retailFlag)))))

def decode (bytes : List UInt8) : Option (QuoteCancellationMarketMemberMessage × List UInt8) := do
  let (sequenceNumber, bytes) ← decodeUIntLE 4 bytes
  let (securityCode, bytes) ← decodeUIntLE 4 bytes
  let (transactionDateAndTime, bytes) ← decodeUIntLE 8 bytes
  let (secondaryOrderId, bytes) ← decodeUIntLE 4 bytes
  let (secondaryOrderId2, bytes) ← decodeUIntLE 4 bytes
  let (retailFlag, bytes) ← decodeUIntLE 1 bytes
  pure ({ sequenceNumber, securityCode, transactionDateAndTime, secondaryOrderId, secondaryOrderId2, retailFlag }, bytes)

@[simp] theorem encode_length (message : QuoteCancellationMarketMemberMessage) : (encode message).length = 25 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : QuoteCancellationMarketMemberMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : QuoteCancellationMarketMemberMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end QuoteCancellationMarketMemberMessage

/-- Trade Market Post Transparency Information Topofbook Message: 55 bytes -/
structure TradeMarketPostTransparencyInformationTopofbookMessage where
  sequenceNumber : BitVec 32
  securityCode : BitVec 32
  transactionDateAndTime : BitVec 64
  marketSegmentId : Alpha 4
  tradingSessionId : BitVec 8
  trdMatchId : BitVec 32
  tradeType : TradeType
  lastPx : BitVec 64
  lastQty : BitVec 32
  grossTradeAmt : BitVec 64
  designation : Designation
  marketMechanism : MarketMechanism
  algoFlag : BitVec 8
  buyerBolsaCode : BuyerBolsaCode
  settlDate : BitVec 32
  transactionCategory : TransactionCategory
  deriving DecidableEq, Repr

namespace TradeMarketPostTransparencyInformationTopofbookMessage

def encode (message : TradeMarketPostTransparencyInformationTopofbookMessage) : List UInt8 :=
  encodeUIntLE 4 message.sequenceNumber
    ++ (encodeUIntLE 4 message.securityCode
    ++ (encodeUIntLE 8 message.transactionDateAndTime
    ++ (Alpha.encode message.marketSegmentId
    ++ (encodeUIntLE 1 message.tradingSessionId
    ++ (encodeUIntLE 4 message.trdMatchId
    ++ (TradeType.encode message.tradeType
    ++ (encodeUIntLE 8 message.lastPx
    ++ (encodeUIntLE 4 message.lastQty
    ++ (encodeUIntLE 8 message.grossTradeAmt
    ++ (Designation.encode message.designation
    ++ (MarketMechanism.encode message.marketMechanism
    ++ (encodeUIntLE 1 message.algoFlag
    ++ (BuyerBolsaCode.encode message.buyerBolsaCode
    ++ (encodeUIntLE 4 message.settlDate
    ++ (TransactionCategory.encode message.transactionCategory)))))))))))))))

def decode (bytes : List UInt8) : Option (TradeMarketPostTransparencyInformationTopofbookMessage × List UInt8) := do
  let (sequenceNumber, bytes) ← decodeUIntLE 4 bytes
  let (securityCode, bytes) ← decodeUIntLE 4 bytes
  let (transactionDateAndTime, bytes) ← decodeUIntLE 8 bytes
  let (marketSegmentId, bytes) ← Alpha.decode 4 bytes
  let (tradingSessionId, bytes) ← decodeUIntLE 1 bytes
  let (trdMatchId, bytes) ← decodeUIntLE 4 bytes
  let (tradeType, bytes) ← TradeType.decode bytes
  let (lastPx, bytes) ← decodeUIntLE 8 bytes
  let (lastQty, bytes) ← decodeUIntLE 4 bytes
  let (grossTradeAmt, bytes) ← decodeUIntLE 8 bytes
  let (designation, bytes) ← Designation.decode bytes
  let (marketMechanism, bytes) ← MarketMechanism.decode bytes
  let (algoFlag, bytes) ← decodeUIntLE 1 bytes
  let (buyerBolsaCode, bytes) ← BuyerBolsaCode.decode bytes
  let (settlDate, bytes) ← decodeUIntLE 4 bytes
  let (transactionCategory, bytes) ← TransactionCategory.decode bytes
  pure ({ sequenceNumber, securityCode, transactionDateAndTime, marketSegmentId, tradingSessionId, trdMatchId, tradeType, lastPx, lastQty, grossTradeAmt, designation, marketMechanism, algoFlag, buyerBolsaCode, settlDate, transactionCategory }, bytes)

@[simp] theorem encode_length (message : TradeMarketPostTransparencyInformationTopofbookMessage) : (encode message).length = 55 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, TradeType.encode_length, Designation.encode_length, MarketMechanism.encode_length, BuyerBolsaCode.encode_length, TransactionCategory.encode_length]

theorem encode_length_pos (message : TradeMarketPostTransparencyInformationTopofbookMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradeMarketPostTransparencyInformationTopofbookMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, TradeType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Designation.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, MarketMechanism.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, BuyerBolsaCode.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [TransactionCategory.decode_encode, some_bind]
  rfl

end TradeMarketPostTransparencyInformationTopofbookMessage

/-- Trade Trade Amendment Or Cancellation Message: 98 bytes -/
structure TradeTradeAmendmentOrCancellationMessage where
  sequenceNumber : BitVec 32
  securityCode : BitVec 32
  transactionDateAndTime : BitVec 64
  marketSegmentId : Alpha 4
  tradingSessionId : BitVec 8
  trdMatchId : BitVec 32
  tradeType : TradeType
  lastPx : BitVec 64
  lastQty : BitVec 32
  grossTradeAmt : BitVec 64
  designation : Designation
  marketMechanism : MarketMechanism
  algoFlag : BitVec 8
  buyerBolsaCode : BuyerBolsaCode
  settlDate : BitVec 32
  transactionCategory : TransactionCategory
  lastChangeFlag : BitVec 8
  bencrfptFlag : BencrfptFlag
  tradePriceCondition : TradePriceCondition
  preTradeTransparencyWaiver : PreTradeTransparencyWaiver
  deferralWaiver : DeferralWaiver
  publishDateAndTime : BitVec 64
  tradeDate : BitVec 64
  tradeSessionDate : BitVec 32
  volumeFloat : BitVec 64
  sicavFundCounterpartySide : SicavFundCounterpartySide
  amendedTradeType : AmendedTradeType
  execRefId : BitVec 32
  amendedTradeDate : BitVec 32
  deriving DecidableEq, Repr

namespace TradeTradeAmendmentOrCancellationMessage

def encode (message : TradeTradeAmendmentOrCancellationMessage) : List UInt8 :=
  encodeUIntLE 4 message.sequenceNumber
    ++ (encodeUIntLE 4 message.securityCode
    ++ (encodeUIntLE 8 message.transactionDateAndTime
    ++ (Alpha.encode message.marketSegmentId
    ++ (encodeUIntLE 1 message.tradingSessionId
    ++ (encodeUIntLE 4 message.trdMatchId
    ++ (TradeType.encode message.tradeType
    ++ (encodeUIntLE 8 message.lastPx
    ++ (encodeUIntLE 4 message.lastQty
    ++ (encodeUIntLE 8 message.grossTradeAmt
    ++ (Designation.encode message.designation
    ++ (MarketMechanism.encode message.marketMechanism
    ++ (encodeUIntLE 1 message.algoFlag
    ++ (BuyerBolsaCode.encode message.buyerBolsaCode
    ++ (encodeUIntLE 4 message.settlDate
    ++ (TransactionCategory.encode message.transactionCategory
    ++ (encodeUIntLE 1 message.lastChangeFlag
    ++ (BencrfptFlag.encode message.bencrfptFlag
    ++ (TradePriceCondition.encode message.tradePriceCondition
    ++ (PreTradeTransparencyWaiver.encode message.preTradeTransparencyWaiver
    ++ (DeferralWaiver.encode message.deferralWaiver
    ++ (encodeUIntLE 8 message.publishDateAndTime
    ++ (encodeUIntLE 8 message.tradeDate
    ++ (encodeUIntLE 4 message.tradeSessionDate
    ++ (encodeUIntLE 8 message.volumeFloat
    ++ (SicavFundCounterpartySide.encode message.sicavFundCounterpartySide
    ++ (AmendedTradeType.encode message.amendedTradeType
    ++ (encodeUIntLE 4 message.execRefId
    ++ (encodeUIntLE 4 message.amendedTradeDate))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (TradeTradeAmendmentOrCancellationMessage × List UInt8) := do
  let (sequenceNumber, bytes) ← decodeUIntLE 4 bytes
  let (securityCode, bytes) ← decodeUIntLE 4 bytes
  let (transactionDateAndTime, bytes) ← decodeUIntLE 8 bytes
  let (marketSegmentId, bytes) ← Alpha.decode 4 bytes
  let (tradingSessionId, bytes) ← decodeUIntLE 1 bytes
  let (trdMatchId, bytes) ← decodeUIntLE 4 bytes
  let (tradeType, bytes) ← TradeType.decode bytes
  let (lastPx, bytes) ← decodeUIntLE 8 bytes
  let (lastQty, bytes) ← decodeUIntLE 4 bytes
  let (grossTradeAmt, bytes) ← decodeUIntLE 8 bytes
  let (designation, bytes) ← Designation.decode bytes
  let (marketMechanism, bytes) ← MarketMechanism.decode bytes
  let (algoFlag, bytes) ← decodeUIntLE 1 bytes
  let (buyerBolsaCode, bytes) ← BuyerBolsaCode.decode bytes
  let (settlDate, bytes) ← decodeUIntLE 4 bytes
  let (transactionCategory, bytes) ← TransactionCategory.decode bytes
  let (lastChangeFlag, bytes) ← decodeUIntLE 1 bytes
  let (bencrfptFlag, bytes) ← BencrfptFlag.decode bytes
  let (tradePriceCondition, bytes) ← TradePriceCondition.decode bytes
  let (preTradeTransparencyWaiver, bytes) ← PreTradeTransparencyWaiver.decode bytes
  let (deferralWaiver, bytes) ← DeferralWaiver.decode bytes
  let (publishDateAndTime, bytes) ← decodeUIntLE 8 bytes
  let (tradeDate, bytes) ← decodeUIntLE 8 bytes
  let (tradeSessionDate, bytes) ← decodeUIntLE 4 bytes
  let (volumeFloat, bytes) ← decodeUIntLE 8 bytes
  let (sicavFundCounterpartySide, bytes) ← SicavFundCounterpartySide.decode bytes
  let (amendedTradeType, bytes) ← AmendedTradeType.decode bytes
  let (execRefId, bytes) ← decodeUIntLE 4 bytes
  let (amendedTradeDate, bytes) ← decodeUIntLE 4 bytes
  pure ({ sequenceNumber, securityCode, transactionDateAndTime, marketSegmentId, tradingSessionId, trdMatchId, tradeType, lastPx, lastQty, grossTradeAmt, designation, marketMechanism, algoFlag, buyerBolsaCode, settlDate, transactionCategory, lastChangeFlag, bencrfptFlag, tradePriceCondition, preTradeTransparencyWaiver, deferralWaiver, publishDateAndTime, tradeDate, tradeSessionDate, volumeFloat, sicavFundCounterpartySide, amendedTradeType, execRefId, amendedTradeDate }, bytes)

@[simp] theorem encode_length (message : TradeTradeAmendmentOrCancellationMessage) : (encode message).length = 98 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, TradeType.encode_length, Designation.encode_length, MarketMechanism.encode_length, BuyerBolsaCode.encode_length, TransactionCategory.encode_length, BencrfptFlag.encode_length, TradePriceCondition.encode_length, PreTradeTransparencyWaiver.encode_length, DeferralWaiver.encode_length, SicavFundCounterpartySide.encode_length, AmendedTradeType.encode_length]

theorem encode_length_pos (message : TradeTradeAmendmentOrCancellationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : TradeTradeAmendmentOrCancellationMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, TradeType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Designation.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, MarketMechanism.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, BuyerBolsaCode.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, TransactionCategory.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, BencrfptFlag.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TradePriceCondition.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, PreTradeTransparencyWaiver.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, DeferralWaiver.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, SicavFundCounterpartySide.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, AmendedTradeType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end TradeTradeAmendmentOrCancellationMessage

/-- Trade Market Post Transparency Information Full Depth Message: 105 bytes -/
structure TradeMarketPostTransparencyInformationFullDepthMessage where
  sequenceNumber : BitVec 32
  securityCode : BitVec 32
  transactionDateAndTime : BitVec 64
  marketSegmentId : Alpha 4
  tradingSessionId : BitVec 8
  trdMatchId : BitVec 32
  tradeType : TradeType
  lastPx : BitVec 64
  lastQty : BitVec 32
  grossTradeAmt : BitVec 64
  designation : Designation
  marketMechanism : MarketMechanism
  algoFlag : BitVec 8
  buyerBolsaCode : BuyerBolsaCode
  settlDate : BitVec 32
  transactionCategory : TransactionCategory
  secondaryOrderId : BitVec 32
  entryDate : BitVec 32
  priority : BitVec 32
  price : BitVec 64
  displayQty : BitVec 32
  retailFlag : BitVec 8
  secondaryOrderId2 : BitVec 32
  entryDate2 : BitVec 32
  priority2 : BitVec 32
  price2 : BitVec 64
  displayQty2 : BitVec 32
  retailFlag2 : BitVec 8
  deriving DecidableEq, Repr

namespace TradeMarketPostTransparencyInformationFullDepthMessage

def encode (message : TradeMarketPostTransparencyInformationFullDepthMessage) : List UInt8 :=
  encodeUIntLE 4 message.sequenceNumber
    ++ (encodeUIntLE 4 message.securityCode
    ++ (encodeUIntLE 8 message.transactionDateAndTime
    ++ (Alpha.encode message.marketSegmentId
    ++ (encodeUIntLE 1 message.tradingSessionId
    ++ (encodeUIntLE 4 message.trdMatchId
    ++ (TradeType.encode message.tradeType
    ++ (encodeUIntLE 8 message.lastPx
    ++ (encodeUIntLE 4 message.lastQty
    ++ (encodeUIntLE 8 message.grossTradeAmt
    ++ (Designation.encode message.designation
    ++ (MarketMechanism.encode message.marketMechanism
    ++ (encodeUIntLE 1 message.algoFlag
    ++ (BuyerBolsaCode.encode message.buyerBolsaCode
    ++ (encodeUIntLE 4 message.settlDate
    ++ (TransactionCategory.encode message.transactionCategory
    ++ (encodeUIntLE 4 message.secondaryOrderId
    ++ (encodeUIntLE 4 message.entryDate
    ++ (encodeUIntLE 4 message.priority
    ++ (encodeUIntLE 8 message.price
    ++ (encodeUIntLE 4 message.displayQty
    ++ (encodeUIntLE 1 message.retailFlag
    ++ (encodeUIntLE 4 message.secondaryOrderId2
    ++ (encodeUIntLE 4 message.entryDate2
    ++ (encodeUIntLE 4 message.priority2
    ++ (encodeUIntLE 8 message.price2
    ++ (encodeUIntLE 4 message.displayQty2
    ++ (encodeUIntLE 1 message.retailFlag2)))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (TradeMarketPostTransparencyInformationFullDepthMessage × List UInt8) := do
  let (sequenceNumber, bytes) ← decodeUIntLE 4 bytes
  let (securityCode, bytes) ← decodeUIntLE 4 bytes
  let (transactionDateAndTime, bytes) ← decodeUIntLE 8 bytes
  let (marketSegmentId, bytes) ← Alpha.decode 4 bytes
  let (tradingSessionId, bytes) ← decodeUIntLE 1 bytes
  let (trdMatchId, bytes) ← decodeUIntLE 4 bytes
  let (tradeType, bytes) ← TradeType.decode bytes
  let (lastPx, bytes) ← decodeUIntLE 8 bytes
  let (lastQty, bytes) ← decodeUIntLE 4 bytes
  let (grossTradeAmt, bytes) ← decodeUIntLE 8 bytes
  let (designation, bytes) ← Designation.decode bytes
  let (marketMechanism, bytes) ← MarketMechanism.decode bytes
  let (algoFlag, bytes) ← decodeUIntLE 1 bytes
  let (buyerBolsaCode, bytes) ← BuyerBolsaCode.decode bytes
  let (settlDate, bytes) ← decodeUIntLE 4 bytes
  let (transactionCategory, bytes) ← TransactionCategory.decode bytes
  let (secondaryOrderId, bytes) ← decodeUIntLE 4 bytes
  let (entryDate, bytes) ← decodeUIntLE 4 bytes
  let (priority, bytes) ← decodeUIntLE 4 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (displayQty, bytes) ← decodeUIntLE 4 bytes
  let (retailFlag, bytes) ← decodeUIntLE 1 bytes
  let (secondaryOrderId2, bytes) ← decodeUIntLE 4 bytes
  let (entryDate2, bytes) ← decodeUIntLE 4 bytes
  let (priority2, bytes) ← decodeUIntLE 4 bytes
  let (price2, bytes) ← decodeUIntLE 8 bytes
  let (displayQty2, bytes) ← decodeUIntLE 4 bytes
  let (retailFlag2, bytes) ← decodeUIntLE 1 bytes
  pure ({ sequenceNumber, securityCode, transactionDateAndTime, marketSegmentId, tradingSessionId, trdMatchId, tradeType, lastPx, lastQty, grossTradeAmt, designation, marketMechanism, algoFlag, buyerBolsaCode, settlDate, transactionCategory, secondaryOrderId, entryDate, priority, price, displayQty, retailFlag, secondaryOrderId2, entryDate2, priority2, price2, displayQty2, retailFlag2 }, bytes)

@[simp] theorem encode_length (message : TradeMarketPostTransparencyInformationFullDepthMessage) : (encode message).length = 105 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, TradeType.encode_length, Designation.encode_length, MarketMechanism.encode_length, BuyerBolsaCode.encode_length, TransactionCategory.encode_length]

theorem encode_length_pos (message : TradeMarketPostTransparencyInformationFullDepthMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : TradeMarketPostTransparencyInformationFullDepthMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, TradeType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Designation.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, MarketMechanism.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, BuyerBolsaCode.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, TransactionCategory.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end TradeMarketPostTransparencyInformationFullDepthMessage

/-- Topofbook Message: 44 bytes -/
structure TopofbookMessage where
  sequenceNumber : BitVec 32
  securityCode : BitVec 32
  transactionDateAndTime : BitVec 64
  bidOrders1 : BitVec 16
  bidSize1 : BitVec 32
  bidPx1 : BitVec 64
  askOrders1 : BitVec 16
  askSize1 : BitVec 32
  askPx1 : BitVec 64
  deriving DecidableEq, Repr

namespace TopofbookMessage

def encode (message : TopofbookMessage) : List UInt8 :=
  encodeUIntLE 4 message.sequenceNumber
    ++ (encodeUIntLE 4 message.securityCode
    ++ (encodeUIntLE 8 message.transactionDateAndTime
    ++ (encodeUIntLE 2 message.bidOrders1
    ++ (encodeUIntLE 4 message.bidSize1
    ++ (encodeUIntLE 8 message.bidPx1
    ++ (encodeUIntLE 2 message.askOrders1
    ++ (encodeUIntLE 4 message.askSize1
    ++ (encodeUIntLE 8 message.askPx1))))))))

def decode (bytes : List UInt8) : Option (TopofbookMessage × List UInt8) := do
  let (sequenceNumber, bytes) ← decodeUIntLE 4 bytes
  let (securityCode, bytes) ← decodeUIntLE 4 bytes
  let (transactionDateAndTime, bytes) ← decodeUIntLE 8 bytes
  let (bidOrders1, bytes) ← decodeUIntLE 2 bytes
  let (bidSize1, bytes) ← decodeUIntLE 4 bytes
  let (bidPx1, bytes) ← decodeUIntLE 8 bytes
  let (askOrders1, bytes) ← decodeUIntLE 2 bytes
  let (askSize1, bytes) ← decodeUIntLE 4 bytes
  let (askPx1, bytes) ← decodeUIntLE 8 bytes
  pure ({ sequenceNumber, securityCode, transactionDateAndTime, bidOrders1, bidSize1, bidPx1, askOrders1, askSize1, askPx1 }, bytes)

@[simp] theorem encode_length (message : TopofbookMessage) : (encode message).length = 44 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : TopofbookMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TopofbookMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end TopofbookMessage

/-- Any Payload, selected by Message Type -/
inductive Payload where
  | logonResponseMessage (message : LogonResponseMessage) -- 8
  | logoutResponseMessage (message : LogoutResponseMessage) -- 11
  | heartbeatMessage (message : HeartbeatMessage) -- 48
  | networkStatusMessage (message : NetworkStatusMessage) -- 10
  | logonMessage (message : LogonMessage) -- 65
  | rejectMessage (message : RejectMessage) -- 13
  | replayRequestMessage (message : ReplayRequestMessage) -- 9
  | replayRequestAckNackMessage (message : ReplayRequestAckNackMessage) -- 12
  | tradingSessionStatusMessage (message : TradingSessionStatusMessage) -- 104
  | newsMessage (message : NewsMessage) -- 66
  | securityListCancellationReportMessage (message : SecurityListCancellationReportMessage) -- 120
  | statisticsMessage (message : StatisticsMessage) -- 132
  | securityListMessage (message : SecurityListMessage) -- 121
  | securityListUpdateReportMessage (message : SecurityListUpdateReportMessage) -- 128
  | securityStatusMessage (message : SecurityStatusMessage) -- 102
  | orderBookClearMessage (message : OrderBookClearMessage) -- 129
  | orderMarketPreTransparencyInformationMessage (message : OrderMarketPreTransparencyInformationMessage) -- 3
  | quoteMarketPreTransparencyInformationMessage (message : QuoteMarketPreTransparencyInformationMessage) -- 7
  | orderCancellationMarketMemberMessage (message : OrderCancellationMarketMemberMessage) -- 1
  | quoteCancellationMarketMemberMessage (message : QuoteCancellationMarketMemberMessage) -- 5
  | tradeMarketPostTransparencyInformationTopofbookMessage (message : TradeMarketPostTransparencyInformationTopofbookMessage) -- 16
  | tradeTradeAmendmentOrCancellationMessage (message : TradeTradeAmendmentOrCancellationMessage) -- 24
  | tradeMarketPostTransparencyInformationFullDepthMessage (message : TradeMarketPostTransparencyInformationFullDepthMessage) -- 17
  | topofbookMessage (message : TopofbookMessage) -- 130
  deriving DecidableEq, Repr

namespace Payload

/-- The Message Type each message is sent under -/
def tag : Payload → BitVec 8
  | .logonResponseMessage _ => 8
  | .logoutResponseMessage _ => 11
  | .heartbeatMessage _ => 48
  | .networkStatusMessage _ => 10
  | .logonMessage _ => 65
  | .rejectMessage _ => 13
  | .replayRequestMessage _ => 9
  | .replayRequestAckNackMessage _ => 12
  | .tradingSessionStatusMessage _ => 104
  | .newsMessage _ => 66
  | .securityListCancellationReportMessage _ => 120
  | .statisticsMessage _ => 132
  | .securityListMessage _ => 121
  | .securityListUpdateReportMessage _ => 128
  | .securityStatusMessage _ => 102
  | .orderBookClearMessage _ => 129
  | .orderMarketPreTransparencyInformationMessage _ => 3
  | .quoteMarketPreTransparencyInformationMessage _ => 7
  | .orderCancellationMarketMemberMessage _ => 1
  | .quoteCancellationMarketMemberMessage _ => 5
  | .tradeMarketPostTransparencyInformationTopofbookMessage _ => 16
  | .tradeTradeAmendmentOrCancellationMessage _ => 24
  | .tradeMarketPostTransparencyInformationFullDepthMessage _ => 17
  | .topofbookMessage _ => 130

def encode : Payload → List UInt8
  | .logonResponseMessage message => LogonResponseMessage.encode message
  | .logoutResponseMessage message => LogoutResponseMessage.encode message
  | .heartbeatMessage message => HeartbeatMessage.encode message
  | .networkStatusMessage message => NetworkStatusMessage.encode message
  | .logonMessage message => LogonMessage.encode message
  | .rejectMessage message => RejectMessage.encode message
  | .replayRequestMessage message => ReplayRequestMessage.encode message
  | .replayRequestAckNackMessage message => ReplayRequestAckNackMessage.encode message
  | .tradingSessionStatusMessage message => TradingSessionStatusMessage.encode message
  | .newsMessage message => NewsMessage.encode message
  | .securityListCancellationReportMessage message => SecurityListCancellationReportMessage.encode message
  | .statisticsMessage message => StatisticsMessage.encode message
  | .securityListMessage message => SecurityListMessage.encode message
  | .securityListUpdateReportMessage message => SecurityListUpdateReportMessage.encode message
  | .securityStatusMessage message => SecurityStatusMessage.encode message
  | .orderBookClearMessage message => OrderBookClearMessage.encode message
  | .orderMarketPreTransparencyInformationMessage message => OrderMarketPreTransparencyInformationMessage.encode message
  | .quoteMarketPreTransparencyInformationMessage message => QuoteMarketPreTransparencyInformationMessage.encode message
  | .orderCancellationMarketMemberMessage message => OrderCancellationMarketMemberMessage.encode message
  | .quoteCancellationMarketMemberMessage message => QuoteCancellationMarketMemberMessage.encode message
  | .tradeMarketPostTransparencyInformationTopofbookMessage message => TradeMarketPostTransparencyInformationTopofbookMessage.encode message
  | .tradeTradeAmendmentOrCancellationMessage message => TradeTradeAmendmentOrCancellationMessage.encode message
  | .tradeMarketPostTransparencyInformationFullDepthMessage message => TradeMarketPostTransparencyInformationFullDepthMessage.encode message
  | .topofbookMessage message => TopofbookMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : Payload) : (encode message).length ≤ 976 := by
  cases message with
  | logonResponseMessage inner =>
    simp only [encode, LogonResponseMessage.encode_length]
    omega
  | logoutResponseMessage inner =>
    simp only [encode, LogoutResponseMessage.encode_length]
    omega
  | heartbeatMessage inner =>
    simp only [encode, HeartbeatMessage.encode_length]
    omega
  | networkStatusMessage inner =>
    simp only [encode, NetworkStatusMessage.encode_length]
    omega
  | logonMessage inner =>
    simp only [encode, LogonMessage.encode_length]
    omega
  | rejectMessage inner =>
    simp only [encode, RejectMessage.encode_length]
    omega
  | replayRequestMessage inner =>
    simp only [encode, ReplayRequestMessage.encode_length]
    omega
  | replayRequestAckNackMessage inner =>
    simp only [encode, ReplayRequestAckNackMessage.encode_length]
    omega
  | tradingSessionStatusMessage inner =>
    simp only [encode, TradingSessionStatusMessage.encode_length]
    omega
  | newsMessage inner =>
    simp only [encode, NewsMessage.encode_length]
    omega
  | securityListCancellationReportMessage inner =>
    simp only [encode, SecurityListCancellationReportMessage.encode_length]
    omega
  | statisticsMessage inner =>
    simp only [encode, StatisticsMessage.encode_length]
    omega
  | securityListMessage inner =>
    simp only [encode, SecurityListMessage.encode_length]
    omega
  | securityListUpdateReportMessage inner =>
    simp only [encode, SecurityListUpdateReportMessage.encode_length]
    omega
  | securityStatusMessage inner =>
    simp only [encode, SecurityStatusMessage.encode_length]
    omega
  | orderBookClearMessage inner =>
    simp only [encode, OrderBookClearMessage.encode_length]
    omega
  | orderMarketPreTransparencyInformationMessage inner =>
    simp only [encode, OrderMarketPreTransparencyInformationMessage.encode_length]
    omega
  | quoteMarketPreTransparencyInformationMessage inner =>
    simp only [encode, QuoteMarketPreTransparencyInformationMessage.encode_length]
    omega
  | orderCancellationMarketMemberMessage inner =>
    simp only [encode, OrderCancellationMarketMemberMessage.encode_length]
    omega
  | quoteCancellationMarketMemberMessage inner =>
    simp only [encode, QuoteCancellationMarketMemberMessage.encode_length]
    omega
  | tradeMarketPostTransparencyInformationTopofbookMessage inner =>
    simp only [encode, TradeMarketPostTransparencyInformationTopofbookMessage.encode_length]
    omega
  | tradeTradeAmendmentOrCancellationMessage inner =>
    simp only [encode, TradeTradeAmendmentOrCancellationMessage.encode_length]
    omega
  | tradeMarketPostTransparencyInformationFullDepthMessage inner =>
    simp only [encode, TradeMarketPostTransparencyInformationFullDepthMessage.encode_length]
    omega
  | topofbookMessage inner =>
    simp only [encode, TopofbookMessage.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (Payload × List UInt8) :=
  if tag = 8 then (LogonResponseMessage.decode bytes).map fun (message, rest) => (.logonResponseMessage message, rest)
  else if tag = 11 then (LogoutResponseMessage.decode bytes).map fun (message, rest) => (.logoutResponseMessage message, rest)
  else if tag = 48 then (HeartbeatMessage.decode bytes).map fun (message, rest) => (.heartbeatMessage message, rest)
  else if tag = 10 then (NetworkStatusMessage.decode bytes).map fun (message, rest) => (.networkStatusMessage message, rest)
  else if tag = 65 then (LogonMessage.decode bytes).map fun (message, rest) => (.logonMessage message, rest)
  else if tag = 13 then (RejectMessage.decode bytes).map fun (message, rest) => (.rejectMessage message, rest)
  else if tag = 9 then (ReplayRequestMessage.decode bytes).map fun (message, rest) => (.replayRequestMessage message, rest)
  else if tag = 12 then (ReplayRequestAckNackMessage.decode bytes).map fun (message, rest) => (.replayRequestAckNackMessage message, rest)
  else if tag = 104 then (TradingSessionStatusMessage.decode bytes).map fun (message, rest) => (.tradingSessionStatusMessage message, rest)
  else if tag = 66 then (NewsMessage.decode bytes).map fun (message, rest) => (.newsMessage message, rest)
  else if tag = 120 then (SecurityListCancellationReportMessage.decode bytes).map fun (message, rest) => (.securityListCancellationReportMessage message, rest)
  else if tag = 132 then (StatisticsMessage.decode bytes).map fun (message, rest) => (.statisticsMessage message, rest)
  else if tag = 121 then (SecurityListMessage.decode bytes).map fun (message, rest) => (.securityListMessage message, rest)
  else if tag = 128 then (SecurityListUpdateReportMessage.decode bytes).map fun (message, rest) => (.securityListUpdateReportMessage message, rest)
  else if tag = 102 then (SecurityStatusMessage.decode bytes).map fun (message, rest) => (.securityStatusMessage message, rest)
  else if tag = 129 then (OrderBookClearMessage.decode bytes).map fun (message, rest) => (.orderBookClearMessage message, rest)
  else if tag = 3 then (OrderMarketPreTransparencyInformationMessage.decode bytes).map fun (message, rest) => (.orderMarketPreTransparencyInformationMessage message, rest)
  else if tag = 7 then (QuoteMarketPreTransparencyInformationMessage.decode bytes).map fun (message, rest) => (.quoteMarketPreTransparencyInformationMessage message, rest)
  else if tag = 1 then (OrderCancellationMarketMemberMessage.decode bytes).map fun (message, rest) => (.orderCancellationMarketMemberMessage message, rest)
  else if tag = 5 then (QuoteCancellationMarketMemberMessage.decode bytes).map fun (message, rest) => (.quoteCancellationMarketMemberMessage message, rest)
  else if tag = 16 then (TradeMarketPostTransparencyInformationTopofbookMessage.decode bytes).map fun (message, rest) => (.tradeMarketPostTransparencyInformationTopofbookMessage message, rest)
  else if tag = 24 then (TradeTradeAmendmentOrCancellationMessage.decode bytes).map fun (message, rest) => (.tradeTradeAmendmentOrCancellationMessage message, rest)
  else if tag = 17 then (TradeMarketPostTransparencyInformationFullDepthMessage.decode bytes).map fun (message, rest) => (.tradeMarketPostTransparencyInformationFullDepthMessage message, rest)
  else if tag = 130 then (TopofbookMessage.decode bytes).map fun (message, rest) => (.topofbookMessage message, rest)
  else none

@[simp] theorem decode_encode (message : Payload) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end Payload

/-- Message -/
structure Message where
  payload : Payload
  deriving DecidableEq, Repr

namespace Message

def encodeBody (message : Message) : List UInt8 :=
  encodeUInt 1 (Payload.tag message.payload)
    ++ (Payload.encode message.payload)

def decodeBody (bytes : List UInt8) : Option (Message × List UInt8) := do
  let (messageType, bytes) ← decodeUInt 1 bytes
  let (payload, bytes) ← Payload.decode messageType bytes
  pure ({ payload }, bytes)

theorem decodeBody_encodeBody (message : Message) (rest : List UInt8) :
    decodeBody (encodeBody message ++ rest) = some (message, rest) := by
  unfold decodeBody encodeBody
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Payload.decode_encode, some_bind]
  rfl

/-- Every body fits the length prefix -/
theorem encodeBody_length_lt (message : Message) : (encodeBody message).length + 2 < 256 ^ 2 := by
  unfold encodeBody
  cases message.payload with
  | logonResponseMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, LogonResponseMessage.encode_length]
    omega
  | logoutResponseMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, LogoutResponseMessage.encode_length]
    omega
  | heartbeatMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, HeartbeatMessage.encode_length]
    omega
  | networkStatusMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, NetworkStatusMessage.encode_length]
    omega
  | logonMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, LogonMessage.encode_length]
    omega
  | rejectMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, RejectMessage.encode_length]
    omega
  | replayRequestMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, ReplayRequestMessage.encode_length]
    omega
  | replayRequestAckNackMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, ReplayRequestAckNackMessage.encode_length]
    omega
  | tradingSessionStatusMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, TradingSessionStatusMessage.encode_length]
    omega
  | newsMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, NewsMessage.encode_length]
    omega
  | securityListCancellationReportMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, SecurityListCancellationReportMessage.encode_length]
    omega
  | statisticsMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, StatisticsMessage.encode_length]
    omega
  | securityListMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, SecurityListMessage.encode_length]
    omega
  | securityListUpdateReportMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, SecurityListUpdateReportMessage.encode_length]
    omega
  | securityStatusMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, SecurityStatusMessage.encode_length]
    omega
  | orderBookClearMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, OrderBookClearMessage.encode_length]
    omega
  | orderMarketPreTransparencyInformationMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, OrderMarketPreTransparencyInformationMessage.encode_length]
    omega
  | quoteMarketPreTransparencyInformationMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, QuoteMarketPreTransparencyInformationMessage.encode_length]
    omega
  | orderCancellationMarketMemberMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, OrderCancellationMarketMemberMessage.encode_length]
    omega
  | quoteCancellationMarketMemberMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, QuoteCancellationMarketMemberMessage.encode_length]
    omega
  | tradeMarketPostTransparencyInformationTopofbookMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, TradeMarketPostTransparencyInformationTopofbookMessage.encode_length]
    omega
  | tradeTradeAmendmentOrCancellationMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, TradeTradeAmendmentOrCancellationMessage.encode_length]
    omega
  | tradeMarketPostTransparencyInformationFullDepthMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, TradeMarketPostTransparencyInformationFullDepthMessage.encode_length]
    omega
  | topofbookMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, TopofbookMessage.encode_length]
    omega

/-- Size rule: Message Size counts the bytes after it plus 2, so it is written from the body and checked on decode -/
def encode : Message → List UInt8 :=
  encodeFramedLE 2 2 encodeBody

def decode : List UInt8 → Option (Message × List UInt8) :=
  decodeFramedLE 2 2 decodeBody

@[simp] theorem decode_encode (message : Message) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) :=
  decodeFramedLE_encodeFramedLE 2 2 encodeBody decodeBody message (decodeBody_encodeBody message) (encodeBody_length_lt message) rest

theorem encode_length_pos (message : Message) : (encode message).length > 0 := by
  unfold encode
  rw [encodeFramedLE_length]
  omega

end Message

/-- Packet -/
structure Packet where
  message : List Message
  deriving DecidableEq, Repr

namespace Packet

def encode (message : Packet) : List UInt8 :=
  encodeMany Message.encode message.message

def decode (bytes : List UInt8) : Option Packet := do
  let message ← decodeAll Message.decode bytes.length bytes
  pure { message }

theorem decode_encode (message : Packet) : decode (encode message) = some message := by
  unfold decode encode
  rw [decodeAll_encodeMany Message.encode Message.decode Message.decode_encode Message.encode_length_pos message.message _ (encodeMany_length_ge Message.encode Message.encode_length_pos message.message), some_bind]
  rfl

end Packet

end Omi.BmeBmeequitiesReplayBmegateV16
