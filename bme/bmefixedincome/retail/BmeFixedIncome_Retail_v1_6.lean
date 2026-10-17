import Wire

/-!
# Bolsas y Mercados Españoles BME Fixed Income Retail Top Of Book v1.6

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.BmeBmefixedincomeRetailBmegateV16

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

/-- Settlement System: one byte code -/
def SettlementSystem.codes : List UInt8 :=
  [0x41, 0x44, 0x4F]

inductive SettlementSystem where
  | iberclearCade -- Iberclear Cade
  | dltBme -- Dlt Bme
  | other -- Other
  | unlisted (byte : { byte : UInt8 // byte ∉ SettlementSystem.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace SettlementSystem

def toByte : SettlementSystem → UInt8
  | .iberclearCade => 0x41
  | .dltBme => 0x44
  | .other => 0x4F
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : SettlementSystem :=
  if byte = 0x41 then .iberclearCade
  else if byte = 0x44 then .dltBme
  else .other

def ofByte (byte : UInt8) : SettlementSystem :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : SettlementSystem) : ofByte value.toByte = value := by
  cases value with
  | iberclearCade => decide
  | dltBme => decide
  | other => decide
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

/-- Coupon Type: one byte code -/
def CouponType.codes : List UInt8 :=
  [0x46, 0x56, 0x20]

inductive CouponType where
  | fixed -- Fixed
  | variable_ -- Variable
  | na -- Na
  | unlisted (byte : { byte : UInt8 // byte ∉ CouponType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace CouponType

def toByte : CouponType → UInt8
  | .fixed => 0x46
  | .variable_ => 0x56
  | .na => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : CouponType :=
  if byte = 0x46 then .fixed
  else if byte = 0x56 then .variable_
  else .na

def ofByte (byte : UInt8) : CouponType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : CouponType) : ofByte value.toByte = value := by
  cases value with
  | fixed => decide
  | variable_ => decide
  | na => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : CouponType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (CouponType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : CouponType) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : CouponType) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : CouponType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end CouponType

/-- Accrued Interest Calculation Procedure: one byte code -/
def AccruedInterestCalculationProcedure.codes : List UInt8 :=
  [0x31]

inductive AccruedInterestCalculationProcedure where
  | realBase -- Real Base
  | unlisted (byte : { byte : UInt8 // byte ∉ AccruedInterestCalculationProcedure.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace AccruedInterestCalculationProcedure

def toByte : AccruedInterestCalculationProcedure → UInt8
  | .realBase => 0x31
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (_ : UInt8) : AccruedInterestCalculationProcedure :=
  .realBase

def ofByte (byte : UInt8) : AccruedInterestCalculationProcedure :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : AccruedInterestCalculationProcedure) : ofByte value.toByte = value := by
  cases value with
  | realBase => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : AccruedInterestCalculationProcedure) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (AccruedInterestCalculationProcedure × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : AccruedInterestCalculationProcedure) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : AccruedInterestCalculationProcedure) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : AccruedInterestCalculationProcedure) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end AccruedInterestCalculationProcedure

/-- Calculation Method: one byte code -/
def CalculationMethod.codes : List UInt8 :=
  [0x30, 0x31, 0x32, 0x33, 0x34, 0x35]

inductive CalculationMethod where
  | t30360Usnasd -- 30360 Usnasd
  | actualActual -- Actual Actual
  | actual360 -- Actual 360
  | actual365 -- Actual 365
  | t30360European -- 30360 European
  | ifDaysToMaturity365Actual360ElseActual365 -- If Days To Maturity 365 Actual 360 Else Actual 365
  | unlisted (byte : { byte : UInt8 // byte ∉ CalculationMethod.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace CalculationMethod

def toByte : CalculationMethod → UInt8
  | .t30360Usnasd => 0x30
  | .actualActual => 0x31
  | .actual360 => 0x32
  | .actual365 => 0x33
  | .t30360European => 0x34
  | .ifDaysToMaturity365Actual360ElseActual365 => 0x35
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : CalculationMethod :=
  if byte = 0x30 then .t30360Usnasd
  else if byte = 0x31 then .actualActual
  else if byte = 0x32 then .actual360
  else if byte = 0x33 then .actual365
  else if byte = 0x34 then .t30360European
  else .ifDaysToMaturity365Actual360ElseActual365

def ofByte (byte : UInt8) : CalculationMethod :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : CalculationMethod) : ofByte value.toByte = value := by
  cases value with
  | t30360Usnasd => decide
  | actualActual => decide
  | actual360 => decide
  | actual365 => decide
  | t30360European => decide
  | ifDaysToMaturity365Actual360ElseActual365 => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : CalculationMethod) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (CalculationMethod × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : CalculationMethod) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : CalculationMethod) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : CalculationMethod) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end CalculationMethod

/-- Price Type: one byte code -/
def PriceType.codes : List UInt8 :=
  [0x31, 0x32]

inductive PriceType where
  | price -- Price
  | rate -- Rate
  | unlisted (byte : { byte : UInt8 // byte ∉ PriceType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace PriceType

def toByte : PriceType → UInt8
  | .price => 0x31
  | .rate => 0x32
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : PriceType :=
  if byte = 0x31 then .price
  else .rate

def ofByte (byte : UInt8) : PriceType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : PriceType) : ofByte value.toByte = value := by
  cases value with
  | price => decide
  | rate => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : PriceType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (PriceType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : PriceType) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : PriceType) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : PriceType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end PriceType

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

/-- Trade Type: one byte code -/
def TradeType.codes : List UInt8 :=
  [0x4D, 0x4B, 0x58, 0x54, 0x51, 0x41, 0x42, 0x43, 0x44, 0x45, 0x46, 0x33]

inductive TradeType where
  | market -- Market
  | blockTrade -- Block Trade
  | cancellation -- Cancellation
  | tradeAmendment -- Trade Amendment
  | application -- Application
  | blockTradeWithSettlementDateEqualToSessionDate -- Block Trade With Settlement Date Equal To Session Date
  | applicationWithSettlementDateEqualToSessionDate -- Application With Settlement Date Equal To Session Date
  | repoBlockTrade -- Repo Block Trade
  | repoApplication -- Repo Application
  | repoBlockTradeWithStartDateEqualToSessionDate -- Repo Block Trade With Start Date Equal To Session Date
  | repoApplicationWithStartDateEqualToSessionDate -- Repo Application With Start Date Equal To Session Date
  | rfq -- Rfq
  | unlisted (byte : { byte : UInt8 // byte ∉ TradeType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TradeType

def toByte : TradeType → UInt8
  | .market => 0x4D
  | .blockTrade => 0x4B
  | .cancellation => 0x58
  | .tradeAmendment => 0x54
  | .application => 0x51
  | .blockTradeWithSettlementDateEqualToSessionDate => 0x41
  | .applicationWithSettlementDateEqualToSessionDate => 0x42
  | .repoBlockTrade => 0x43
  | .repoApplication => 0x44
  | .repoBlockTradeWithStartDateEqualToSessionDate => 0x45
  | .repoApplicationWithStartDateEqualToSessionDate => 0x46
  | .rfq => 0x33
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TradeType :=
  if byte = 0x4D then .market
  else if byte = 0x4B then .blockTrade
  else if byte = 0x58 then .cancellation
  else if byte = 0x54 then .tradeAmendment
  else if byte = 0x51 then .application
  else if byte = 0x41 then .blockTradeWithSettlementDateEqualToSessionDate
  else if byte = 0x42 then .applicationWithSettlementDateEqualToSessionDate
  else if byte = 0x43 then .repoBlockTrade
  else if byte = 0x44 then .repoApplication
  else if byte = 0x45 then .repoBlockTradeWithStartDateEqualToSessionDate
  else if byte = 0x46 then .repoApplicationWithStartDateEqualToSessionDate
  else .rfq

def ofByte (byte : UInt8) : TradeType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TradeType) : ofByte value.toByte = value := by
  cases value with
  | market => decide
  | blockTrade => decide
  | cancellation => decide
  | tradeAmendment => decide
  | application => decide
  | blockTradeWithSettlementDateEqualToSessionDate => decide
  | applicationWithSettlementDateEqualToSessionDate => decide
  | repoBlockTrade => decide
  | repoApplication => decide
  | repoBlockTradeWithStartDateEqualToSessionDate => decide
  | repoApplicationWithStartDateEqualToSessionDate => decide
  | rfq => decide
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
  [0x30, 0x31, 0x36]

inductive MarketMechanism where
  | centralLimitOrderBook -- Central Limit Order Book
  | offBookMessagingTrading -- Off Book Messaging Trading
  | requestForQuotes -- Request For Quotes
  | unlisted (byte : { byte : UInt8 // byte ∉ MarketMechanism.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace MarketMechanism

def toByte : MarketMechanism → UInt8
  | .centralLimitOrderBook => 0x30
  | .offBookMessagingTrading => 0x31
  | .requestForQuotes => 0x36
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : MarketMechanism :=
  if byte = 0x30 then .centralLimitOrderBook
  else if byte = 0x31 then .offBookMessagingTrading
  else .requestForQuotes

def ofByte (byte : UInt8) : MarketMechanism :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : MarketMechanism) : ofByte value.toByte = value := by
  cases value with
  | centralLimitOrderBook => decide
  | offBookMessagingTrading => decide
  | requestForQuotes => decide
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

/-- Transaction Category: one byte code -/
def TransactionCategory.codes : List UInt8 :=
  [0x20, 0x5A]

inductive TransactionCategory where
  | normalCategory -- Normal Category
  | packageTradeExcludingExchangeForPhysicalsTpac -- Package Trade Excluding Exchange For Physicals Tpac
  | unlisted (byte : { byte : UInt8 // byte ∉ TransactionCategory.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TransactionCategory

def toByte : TransactionCategory → UInt8
  | .normalCategory => 0x20
  | .packageTradeExcludingExchangeForPhysicalsTpac => 0x5A
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TransactionCategory :=
  if byte = 0x20 then .normalCategory
  else .packageTradeExcludingExchangeForPhysicalsTpac

def ofByte (byte : UInt8) : TransactionCategory :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TransactionCategory) : ofByte value.toByte = value := by
  cases value with
  | normalCategory => decide
  | packageTradeExcludingExchangeForPhysicalsTpac => decide
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
  [0x20, 0x36]

inductive BencrfptFlag where
  | normalTrade -- Normal Trade
  | benchmarkTradeBenc -- Benchmark Trade Benc
  | unlisted (byte : { byte : UInt8 // byte ∉ BencrfptFlag.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace BencrfptFlag

def toByte : BencrfptFlag → UInt8
  | .normalTrade => 0x20
  | .benchmarkTradeBenc => 0x36
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : BencrfptFlag :=
  if byte = 0x20 then .normalTrade
  else .benchmarkTradeBenc

def ofByte (byte : UInt8) : BencrfptFlag :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : BencrfptFlag) : ofByte value.toByte = value := by
  cases value with
  | normalTrade => decide
  | benchmarkTradeBenc => decide
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
  [0x20, 0x35, 0x5A]

inductive TradePriceCondition where
  | plainVanillaTrade -- Plain Vanilla Trade
  | nonPriceFormingTradeFormerlyDefinedAsATechnicalTradeNpft -- Non Price Forming Trade Formerly Defined As A Technical Trade Npft
  | priceIsNotApplicableNoap -- Price Is Not Applicable Noap
  | unlisted (byte : { byte : UInt8 // byte ∉ TradePriceCondition.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TradePriceCondition

def toByte : TradePriceCondition → UInt8
  | .plainVanillaTrade => 0x20
  | .nonPriceFormingTradeFormerlyDefinedAsATechnicalTradeNpft => 0x35
  | .priceIsNotApplicableNoap => 0x5A
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TradePriceCondition :=
  if byte = 0x20 then .plainVanillaTrade
  else if byte = 0x35 then .nonPriceFormingTradeFormerlyDefinedAsATechnicalTradeNpft
  else .priceIsNotApplicableNoap

def ofByte (byte : UInt8) : TradePriceCondition :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TradePriceCondition) : ofByte value.toByte = value := by
  cases value with
  | plainVanillaTrade => decide
  | nonPriceFormingTradeFormerlyDefinedAsATechnicalTradeNpft => decide
  | priceIsNotApplicableNoap => decide
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
  [0x20]

inductive PreTradeTransparencyWaiver where
  | negotiatedTradeNego -- Negotiated Trade Nego
  | unlisted (byte : { byte : UInt8 // byte ∉ PreTradeTransparencyWaiver.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace PreTradeTransparencyWaiver

def toByte : PreTradeTransparencyWaiver → UInt8
  | .negotiatedTradeNego => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (_ : UInt8) : PreTradeTransparencyWaiver :=
  .negotiatedTradeNego

def ofByte (byte : UInt8) : PreTradeTransparencyWaiver :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : PreTradeTransparencyWaiver) : ofByte value.toByte = value := by
  cases value with
  | negotiatedTradeNego => decide
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
  [0x20, 0x41, 0x42, 0x43, 0x44, 0x45, 0x46, 0x47]

inductive DeferralWaiver where
  | immediatePublication -- Immediate Publication
  | nonImmediatePublicationDeferralForMediumSizeLiquidMarketMlf1 -- Non Immediate Publication Deferral For Medium Size Liquid Market Mlf 1
  | nonImmediatePublicationDeferralForMediumSizeIlliquidMarketMif2 -- Non Immediate Publication Deferral For Medium Size Illiquid Market Mif 2
  | nonImmediatePublicationDeferralForLargeSizeLiquidMarketLlf3 -- Non Immediate Publication Deferral For Large Size Liquid Market Llf 3
  | nonImmediatePublicationDeferralForLargeSizeIlliquidMarketLif4 -- Non Immediate Publication Deferral For Large Size Illiquid Market Lif 4
  | nonImmediatePublicationDeferralForVeryLargeSizeLiquidMarketVlf5 -- Non Immediate Publication Deferral For Very Large Size Liquid Market Vlf 5
  | nonImmediatePublicationDeferralForVeryLargeSizeIlliquidMarketVif5 -- Non Immediate Publication Deferral For Very Large Size Illiquid Market Vif 5
  | nonImmediatePublicationDeferralForEtCsEtNsSfPsEmissionAllowancesDeff -- Non Immediate Publication Deferral For Et Cs Et Ns Sf Ps Emission Allowances Deff
  | unlisted (byte : { byte : UInt8 // byte ∉ DeferralWaiver.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace DeferralWaiver

def toByte : DeferralWaiver → UInt8
  | .immediatePublication => 0x20
  | .nonImmediatePublicationDeferralForMediumSizeLiquidMarketMlf1 => 0x41
  | .nonImmediatePublicationDeferralForMediumSizeIlliquidMarketMif2 => 0x42
  | .nonImmediatePublicationDeferralForLargeSizeLiquidMarketLlf3 => 0x43
  | .nonImmediatePublicationDeferralForLargeSizeIlliquidMarketLif4 => 0x44
  | .nonImmediatePublicationDeferralForVeryLargeSizeLiquidMarketVlf5 => 0x45
  | .nonImmediatePublicationDeferralForVeryLargeSizeIlliquidMarketVif5 => 0x46
  | .nonImmediatePublicationDeferralForEtCsEtNsSfPsEmissionAllowancesDeff => 0x47
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : DeferralWaiver :=
  if byte = 0x20 then .immediatePublication
  else if byte = 0x41 then .nonImmediatePublicationDeferralForMediumSizeLiquidMarketMlf1
  else if byte = 0x42 then .nonImmediatePublicationDeferralForMediumSizeIlliquidMarketMif2
  else if byte = 0x43 then .nonImmediatePublicationDeferralForLargeSizeLiquidMarketLlf3
  else if byte = 0x44 then .nonImmediatePublicationDeferralForLargeSizeIlliquidMarketLif4
  else if byte = 0x45 then .nonImmediatePublicationDeferralForVeryLargeSizeLiquidMarketVlf5
  else if byte = 0x46 then .nonImmediatePublicationDeferralForVeryLargeSizeIlliquidMarketVif5
  else .nonImmediatePublicationDeferralForEtCsEtNsSfPsEmissionAllowancesDeff

def ofByte (byte : UInt8) : DeferralWaiver :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : DeferralWaiver) : ofByte value.toByte = value := by
  cases value with
  | immediatePublication => decide
  | nonImmediatePublicationDeferralForMediumSizeLiquidMarketMlf1 => decide
  | nonImmediatePublicationDeferralForMediumSizeIlliquidMarketMif2 => decide
  | nonImmediatePublicationDeferralForLargeSizeLiquidMarketLlf3 => decide
  | nonImmediatePublicationDeferralForLargeSizeIlliquidMarketLif4 => decide
  | nonImmediatePublicationDeferralForVeryLargeSizeLiquidMarketVlf5 => decide
  | nonImmediatePublicationDeferralForVeryLargeSizeIlliquidMarketVif5 => decide
  | nonImmediatePublicationDeferralForEtCsEtNsSfPsEmissionAllowancesDeff => decide
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

/-- Post Deferral Publication Type: one byte code -/
def PostDeferralPublicationType.codes : List UInt8 :=
  [0x20]

inductive PostDeferralPublicationType where
  | notApplicableNoRelevantDeferralOrEnrichmentType -- Not Applicable No Relevant Deferral Or Enrichment Type
  | unlisted (byte : { byte : UInt8 // byte ∉ PostDeferralPublicationType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace PostDeferralPublicationType

def toByte : PostDeferralPublicationType → UInt8
  | .notApplicableNoRelevantDeferralOrEnrichmentType => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (_ : UInt8) : PostDeferralPublicationType :=
  .notApplicableNoRelevantDeferralOrEnrichmentType

def ofByte (byte : UInt8) : PostDeferralPublicationType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : PostDeferralPublicationType) : ofByte value.toByte = value := by
  cases value with
  | notApplicableNoRelevantDeferralOrEnrichmentType => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : PostDeferralPublicationType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (PostDeferralPublicationType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : PostDeferralPublicationType) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : PostDeferralPublicationType) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : PostDeferralPublicationType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end PostDeferralPublicationType

/-- Amended Trade Type: one byte code -/
def AmendedTradeType.codes : List UInt8 :=
  [0x4D, 0x4B, 0x58, 0x54, 0x51, 0x41, 0x42, 0x43, 0x44, 0x45, 0x46, 0x33]

inductive AmendedTradeType where
  | market -- Market
  | blockTrade -- Block Trade
  | cancellation -- Cancellation
  | tradeAmendment -- Trade Amendment
  | application -- Application
  | blockTradeWithSettlementDateEqualToSessionDate -- Block Trade With Settlement Date Equal To Session Date
  | applicationWithSettlementDateEqualToSessionDate -- Application With Settlement Date Equal To Session Date
  | repoBlockTrade -- Repo Block Trade
  | repoApplication -- Repo Application
  | repoBlockTradeWithStartDateEqualToSessionDate -- Repo Block Trade With Start Date Equal To Session Date
  | repoApplicationWithStartDateEqualToSessionDate -- Repo Application With Start Date Equal To Session Date
  | rfq -- Rfq
  | unlisted (byte : { byte : UInt8 // byte ∉ AmendedTradeType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace AmendedTradeType

def toByte : AmendedTradeType → UInt8
  | .market => 0x4D
  | .blockTrade => 0x4B
  | .cancellation => 0x58
  | .tradeAmendment => 0x54
  | .application => 0x51
  | .blockTradeWithSettlementDateEqualToSessionDate => 0x41
  | .applicationWithSettlementDateEqualToSessionDate => 0x42
  | .repoBlockTrade => 0x43
  | .repoApplication => 0x44
  | .repoBlockTradeWithStartDateEqualToSessionDate => 0x45
  | .repoApplicationWithStartDateEqualToSessionDate => 0x46
  | .rfq => 0x33
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : AmendedTradeType :=
  if byte = 0x4D then .market
  else if byte = 0x4B then .blockTrade
  else if byte = 0x58 then .cancellation
  else if byte = 0x54 then .tradeAmendment
  else if byte = 0x51 then .application
  else if byte = 0x41 then .blockTradeWithSettlementDateEqualToSessionDate
  else if byte = 0x42 then .applicationWithSettlementDateEqualToSessionDate
  else if byte = 0x43 then .repoBlockTrade
  else if byte = 0x44 then .repoApplication
  else if byte = 0x45 then .repoBlockTradeWithStartDateEqualToSessionDate
  else if byte = 0x46 then .repoApplicationWithStartDateEqualToSessionDate
  else .rfq

def ofByte (byte : UInt8) : AmendedTradeType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : AmendedTradeType) : ofByte value.toByte = value := by
  cases value with
  | market => decide
  | blockTrade => decide
  | cancellation => decide
  | tradeAmendment => decide
  | application => decide
  | blockTradeWithSettlementDateEqualToSessionDate => decide
  | applicationWithSettlementDateEqualToSessionDate => decide
  | repoBlockTrade => decide
  | repoApplication => decide
  | repoBlockTradeWithStartDateEqualToSessionDate => decide
  | repoApplicationWithStartDateEqualToSessionDate => decide
  | rfq => decide
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

/-- Ioi Trans Type: one byte code -/
def IoiTransType.codes : List UInt8 :=
  [0x4E, 0x43, 0x52]

inductive IoiTransType where
  | new -- New
  | cancel -- Cancel
  | replace -- Replace
  | unlisted (byte : { byte : UInt8 // byte ∉ IoiTransType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace IoiTransType

def toByte : IoiTransType → UInt8
  | .new => 0x4E
  | .cancel => 0x43
  | .replace => 0x52
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : IoiTransType :=
  if byte = 0x4E then .new
  else if byte = 0x43 then .cancel
  else .replace

def ofByte (byte : UInt8) : IoiTransType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : IoiTransType) : ofByte value.toByte = value := by
  cases value with
  | new => decide
  | cancel => decide
  | replace => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : IoiTransType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (IoiTransType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : IoiTransType) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : IoiTransType) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : IoiTransType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end IoiTransType

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

/-- Security List Message: 450 bytes -/
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
  securityStatus : SecurityStatus
  couponPaymentDate : BitVec 32
  minPriceIncrement : BitVec 64
  numberOfDecimals : BitVec 8
  orderNumberOfDecimals : BitVec 8
  couponRate : BitVec 64
  issuer : Alpha 12
  tradingScopeB1 : BitVec 8
  firstTradingDate : BitVec 32
  settlementSystem : SettlementSystem
  maturity : BitVec 64
  couponPeriodicity : BitVec 8
  benchmark : BitVec 8
  strippable : BitVec 8
  volumeIssued : BitVec 64
  aliveVolume : BitVec 64
  couponType : CouponType
  couponQuotation : BitVec 8
  accruedInterestCalculationProcedure : AccruedInterestCalculationProcedure
  nextRedemptionDate : BitVec 32
  typeOfRedemption : Alpha 2
  facial : BitVec 64
  calculationMethod : CalculationMethod
  dateLastCouponWasPaid : BitVec 32
  bondSeniority : Alpha 4
  interestAccrualDate : BitVec 32
  startDate : BitVec 32
  priceType : PriceType
  spreadToIndex : BitVec 64
  benchmarkCurvePointsUnits : Alpha 4
  benchmarkCurvePointsValue : BitVec 8
  benchmarkSecurityId : Alpha 25
  accruedInterestRateR8 : BitVec 64
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
    ++ (SecurityStatus.encode message.securityStatus
    ++ (encodeUIntLE 4 message.couponPaymentDate
    ++ (encodeUIntLE 8 message.minPriceIncrement
    ++ (encodeUIntLE 1 message.numberOfDecimals
    ++ (encodeUIntLE 1 message.orderNumberOfDecimals
    ++ (encodeUIntLE 8 message.couponRate
    ++ (Alpha.encode message.issuer
    ++ (encodeUIntLE 1 message.tradingScopeB1
    ++ (encodeUIntLE 4 message.firstTradingDate
    ++ (SettlementSystem.encode message.settlementSystem
    ++ (encodeUIntLE 8 message.maturity
    ++ (encodeUIntLE 1 message.couponPeriodicity
    ++ (encodeUIntLE 1 message.benchmark
    ++ (encodeUIntLE 1 message.strippable
    ++ (encodeUIntLE 8 message.volumeIssued
    ++ (encodeUIntLE 8 message.aliveVolume
    ++ (CouponType.encode message.couponType
    ++ (encodeUIntLE 1 message.couponQuotation
    ++ (AccruedInterestCalculationProcedure.encode message.accruedInterestCalculationProcedure
    ++ (encodeUIntLE 4 message.nextRedemptionDate
    ++ (Alpha.encode message.typeOfRedemption
    ++ (encodeUIntLE 8 message.facial
    ++ (CalculationMethod.encode message.calculationMethod
    ++ (encodeUIntLE 4 message.dateLastCouponWasPaid
    ++ (Alpha.encode message.bondSeniority
    ++ (encodeUIntLE 4 message.interestAccrualDate
    ++ (encodeUIntLE 4 message.startDate
    ++ (PriceType.encode message.priceType
    ++ (encodeUIntLE 8 message.spreadToIndex
    ++ (Alpha.encode message.benchmarkCurvePointsUnits
    ++ (encodeUIntLE 1 message.benchmarkCurvePointsValue
    ++ (Alpha.encode message.benchmarkSecurityId
    ++ (encodeUIntLE 8 message.accruedInterestRateR8)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

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
  let (securityStatus, bytes) ← SecurityStatus.decode bytes
  let (couponPaymentDate, bytes) ← decodeUIntLE 4 bytes
  let (minPriceIncrement, bytes) ← decodeUIntLE 8 bytes
  let (numberOfDecimals, bytes) ← decodeUIntLE 1 bytes
  let (orderNumberOfDecimals, bytes) ← decodeUIntLE 1 bytes
  let (couponRate, bytes) ← decodeUIntLE 8 bytes
  let (issuer, bytes) ← Alpha.decode 12 bytes
  let (tradingScopeB1, bytes) ← decodeUIntLE 1 bytes
  let (firstTradingDate, bytes) ← decodeUIntLE 4 bytes
  let (settlementSystem, bytes) ← SettlementSystem.decode bytes
  let (maturity, bytes) ← decodeUIntLE 8 bytes
  let (couponPeriodicity, bytes) ← decodeUIntLE 1 bytes
  let (benchmark, bytes) ← decodeUIntLE 1 bytes
  let (strippable, bytes) ← decodeUIntLE 1 bytes
  let (volumeIssued, bytes) ← decodeUIntLE 8 bytes
  let (aliveVolume, bytes) ← decodeUIntLE 8 bytes
  let (couponType, bytes) ← CouponType.decode bytes
  let (couponQuotation, bytes) ← decodeUIntLE 1 bytes
  let (accruedInterestCalculationProcedure, bytes) ← AccruedInterestCalculationProcedure.decode bytes
  let (nextRedemptionDate, bytes) ← decodeUIntLE 4 bytes
  let (typeOfRedemption, bytes) ← Alpha.decode 2 bytes
  let (facial, bytes) ← decodeUIntLE 8 bytes
  let (calculationMethod, bytes) ← CalculationMethod.decode bytes
  let (dateLastCouponWasPaid, bytes) ← decodeUIntLE 4 bytes
  let (bondSeniority, bytes) ← Alpha.decode 4 bytes
  let (interestAccrualDate, bytes) ← decodeUIntLE 4 bytes
  let (startDate, bytes) ← decodeUIntLE 4 bytes
  let (priceType, bytes) ← PriceType.decode bytes
  let (spreadToIndex, bytes) ← decodeUIntLE 8 bytes
  let (benchmarkCurvePointsUnits, bytes) ← Alpha.decode 4 bytes
  let (benchmarkCurvePointsValue, bytes) ← decodeUIntLE 1 bytes
  let (benchmarkSecurityId, bytes) ← Alpha.decode 25 bytes
  let (accruedInterestRateR8, bytes) ← decodeUIntLE 8 bytes
  pure ({ sequenceNumber, marketId, marketSegmentId, securityCode, symbol, symbolIsin, fisn, issuerLei, securityGroup, cfiCode, securityType, maturityDate, issueDate, contractMultiplier, liSpre, sstIpre, liSpost, sstIpost, liquidInstrument, admissionRequestedByIssuer, minTradeVol, roundLot, currency, modalityMaskB4, securityDescription, tradingObligation, securityName, securityStatus, couponPaymentDate, minPriceIncrement, numberOfDecimals, orderNumberOfDecimals, couponRate, issuer, tradingScopeB1, firstTradingDate, settlementSystem, maturity, couponPeriodicity, benchmark, strippable, volumeIssued, aliveVolume, couponType, couponQuotation, accruedInterestCalculationProcedure, nextRedemptionDate, typeOfRedemption, facial, calculationMethod, dateLastCouponWasPaid, bondSeniority, interestAccrualDate, startDate, priceType, spreadToIndex, benchmarkCurvePointsUnits, benchmarkCurvePointsValue, benchmarkSecurityId, accruedInterestRateR8 }, bytes)

@[simp] theorem encode_length (message : SecurityListMessage) : (encode message).length = 450 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, SecurityStatus.encode_length, SettlementSystem.encode_length, CouponType.encode_length, AccruedInterestCalculationProcedure.encode_length, CalculationMethod.encode_length, PriceType.encode_length]

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
  rw [List.append_assoc, SecurityStatus.decode_encode, some_bind]
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
  rw [List.append_assoc, CouponType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, AccruedInterestCalculationProcedure.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, CalculationMethod.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, PriceType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end SecurityListMessage

/-- Security List Update Report Message: 450 bytes -/
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
  securityStatus : SecurityStatus
  couponPaymentDate : BitVec 32
  minPriceIncrement : BitVec 64
  numberOfDecimals : BitVec 8
  orderNumberOfDecimals : BitVec 8
  couponRate : BitVec 64
  issuer : Alpha 12
  tradingScopeB1 : BitVec 8
  firstTradingDate : BitVec 32
  settlementSystem : SettlementSystem
  maturity : BitVec 64
  couponPeriodicity : BitVec 8
  benchmark : BitVec 8
  strippable : BitVec 8
  volumeIssued : BitVec 64
  aliveVolume : BitVec 64
  couponType : CouponType
  couponQuotation : BitVec 8
  accruedInterestCalculationProcedure : AccruedInterestCalculationProcedure
  nextRedemptionDate : BitVec 32
  typeOfRedemption : Alpha 2
  facial : BitVec 64
  calculationMethod : CalculationMethod
  dateLastCouponWasPaid : BitVec 32
  bondSeniority : Alpha 4
  interestAccrualDate : BitVec 32
  startDate : BitVec 32
  priceType : PriceType
  spreadToIndex : BitVec 64
  benchmarkCurvePointsUnits : Alpha 4
  benchmarkCurvePointsValue : BitVec 8
  benchmarkSecurityId : Alpha 25
  accruedInterestRateR8 : BitVec 64
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
    ++ (SecurityStatus.encode message.securityStatus
    ++ (encodeUIntLE 4 message.couponPaymentDate
    ++ (encodeUIntLE 8 message.minPriceIncrement
    ++ (encodeUIntLE 1 message.numberOfDecimals
    ++ (encodeUIntLE 1 message.orderNumberOfDecimals
    ++ (encodeUIntLE 8 message.couponRate
    ++ (Alpha.encode message.issuer
    ++ (encodeUIntLE 1 message.tradingScopeB1
    ++ (encodeUIntLE 4 message.firstTradingDate
    ++ (SettlementSystem.encode message.settlementSystem
    ++ (encodeUIntLE 8 message.maturity
    ++ (encodeUIntLE 1 message.couponPeriodicity
    ++ (encodeUIntLE 1 message.benchmark
    ++ (encodeUIntLE 1 message.strippable
    ++ (encodeUIntLE 8 message.volumeIssued
    ++ (encodeUIntLE 8 message.aliveVolume
    ++ (CouponType.encode message.couponType
    ++ (encodeUIntLE 1 message.couponQuotation
    ++ (AccruedInterestCalculationProcedure.encode message.accruedInterestCalculationProcedure
    ++ (encodeUIntLE 4 message.nextRedemptionDate
    ++ (Alpha.encode message.typeOfRedemption
    ++ (encodeUIntLE 8 message.facial
    ++ (CalculationMethod.encode message.calculationMethod
    ++ (encodeUIntLE 4 message.dateLastCouponWasPaid
    ++ (Alpha.encode message.bondSeniority
    ++ (encodeUIntLE 4 message.interestAccrualDate
    ++ (encodeUIntLE 4 message.startDate
    ++ (PriceType.encode message.priceType
    ++ (encodeUIntLE 8 message.spreadToIndex
    ++ (Alpha.encode message.benchmarkCurvePointsUnits
    ++ (encodeUIntLE 1 message.benchmarkCurvePointsValue
    ++ (Alpha.encode message.benchmarkSecurityId
    ++ (encodeUIntLE 8 message.accruedInterestRateR8)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

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
  let (securityStatus, bytes) ← SecurityStatus.decode bytes
  let (couponPaymentDate, bytes) ← decodeUIntLE 4 bytes
  let (minPriceIncrement, bytes) ← decodeUIntLE 8 bytes
  let (numberOfDecimals, bytes) ← decodeUIntLE 1 bytes
  let (orderNumberOfDecimals, bytes) ← decodeUIntLE 1 bytes
  let (couponRate, bytes) ← decodeUIntLE 8 bytes
  let (issuer, bytes) ← Alpha.decode 12 bytes
  let (tradingScopeB1, bytes) ← decodeUIntLE 1 bytes
  let (firstTradingDate, bytes) ← decodeUIntLE 4 bytes
  let (settlementSystem, bytes) ← SettlementSystem.decode bytes
  let (maturity, bytes) ← decodeUIntLE 8 bytes
  let (couponPeriodicity, bytes) ← decodeUIntLE 1 bytes
  let (benchmark, bytes) ← decodeUIntLE 1 bytes
  let (strippable, bytes) ← decodeUIntLE 1 bytes
  let (volumeIssued, bytes) ← decodeUIntLE 8 bytes
  let (aliveVolume, bytes) ← decodeUIntLE 8 bytes
  let (couponType, bytes) ← CouponType.decode bytes
  let (couponQuotation, bytes) ← decodeUIntLE 1 bytes
  let (accruedInterestCalculationProcedure, bytes) ← AccruedInterestCalculationProcedure.decode bytes
  let (nextRedemptionDate, bytes) ← decodeUIntLE 4 bytes
  let (typeOfRedemption, bytes) ← Alpha.decode 2 bytes
  let (facial, bytes) ← decodeUIntLE 8 bytes
  let (calculationMethod, bytes) ← CalculationMethod.decode bytes
  let (dateLastCouponWasPaid, bytes) ← decodeUIntLE 4 bytes
  let (bondSeniority, bytes) ← Alpha.decode 4 bytes
  let (interestAccrualDate, bytes) ← decodeUIntLE 4 bytes
  let (startDate, bytes) ← decodeUIntLE 4 bytes
  let (priceType, bytes) ← PriceType.decode bytes
  let (spreadToIndex, bytes) ← decodeUIntLE 8 bytes
  let (benchmarkCurvePointsUnits, bytes) ← Alpha.decode 4 bytes
  let (benchmarkCurvePointsValue, bytes) ← decodeUIntLE 1 bytes
  let (benchmarkSecurityId, bytes) ← Alpha.decode 25 bytes
  let (accruedInterestRateR8, bytes) ← decodeUIntLE 8 bytes
  pure ({ sequenceNumber, marketId, marketSegmentId, securityCode, symbol, symbolIsin, fisn, issuerLei, securityGroup, cfiCode, securityType, maturityDate, issueDate, contractMultiplier, liSpre, sstIpre, liSpost, sstIpost, liquidInstrument, admissionRequestedByIssuer, minTradeVol, roundLot, currency, modalityMaskB4, securityDescription, tradingObligation, securityName, securityStatus, couponPaymentDate, minPriceIncrement, numberOfDecimals, orderNumberOfDecimals, couponRate, issuer, tradingScopeB1, firstTradingDate, settlementSystem, maturity, couponPeriodicity, benchmark, strippable, volumeIssued, aliveVolume, couponType, couponQuotation, accruedInterestCalculationProcedure, nextRedemptionDate, typeOfRedemption, facial, calculationMethod, dateLastCouponWasPaid, bondSeniority, interestAccrualDate, startDate, priceType, spreadToIndex, benchmarkCurvePointsUnits, benchmarkCurvePointsValue, benchmarkSecurityId, accruedInterestRateR8 }, bytes)

@[simp] theorem encode_length (message : SecurityListUpdateReportMessage) : (encode message).length = 450 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, SecurityStatus.encode_length, SettlementSystem.encode_length, CouponType.encode_length, AccruedInterestCalculationProcedure.encode_length, CalculationMethod.encode_length, PriceType.encode_length]

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
  rw [List.append_assoc, SecurityStatus.decode_encode, some_bind]
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
  rw [List.append_assoc, CouponType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, AccruedInterestCalculationProcedure.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, CalculationMethod.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, PriceType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end SecurityListUpdateReportMessage

/-- Security Status Message: 59 bytes -/
structure SecurityStatusMessage where
  sequenceNumber : BitVec 32
  securityCode : BitVec 32
  transactionDateAndTime : BitVec 64
  referencePrice : BitVec 64
  securityTradingStatus : BitVec 8
  nonAvailabilityReason : BitVec 8
  highLimitPrice : BitVec 64
  lowLimitPrice : BitVec 64
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
    ++ (encodeUIntLE 1 message.securityTradingStatus
    ++ (encodeUIntLE 1 message.nonAvailabilityReason
    ++ (encodeUIntLE 8 message.highLimitPrice
    ++ (encodeUIntLE 8 message.lowLimitPrice
    ++ (StaticRangeType.encode message.staticRangeType
    ++ (encodeUIntLE 8 message.orderStaticRange
    ++ (encodeUIntLE 8 message.blockStaticRange))))))))))

def decode (bytes : List UInt8) : Option (SecurityStatusMessage × List UInt8) := do
  let (sequenceNumber, bytes) ← decodeUIntLE 4 bytes
  let (securityCode, bytes) ← decodeUIntLE 4 bytes
  let (transactionDateAndTime, bytes) ← decodeUIntLE 8 bytes
  let (referencePrice, bytes) ← decodeUIntLE 8 bytes
  let (securityTradingStatus, bytes) ← decodeUIntLE 1 bytes
  let (nonAvailabilityReason, bytes) ← decodeUIntLE 1 bytes
  let (highLimitPrice, bytes) ← decodeUIntLE 8 bytes
  let (lowLimitPrice, bytes) ← decodeUIntLE 8 bytes
  let (staticRangeType, bytes) ← StaticRangeType.decode bytes
  let (orderStaticRange, bytes) ← decodeUIntLE 8 bytes
  let (blockStaticRange, bytes) ← decodeUIntLE 8 bytes
  pure ({ sequenceNumber, securityCode, transactionDateAndTime, referencePrice, securityTradingStatus, nonAvailabilityReason, highLimitPrice, lowLimitPrice, staticRangeType, orderStaticRange, blockStaticRange }, bytes)

@[simp] theorem encode_length (message : SecurityStatusMessage) : (encode message).length = 59 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, StaticRangeType.encode_length]

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
  rw [List.append_assoc, StaticRangeType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end SecurityStatusMessage

/-- Trade Market Post Transparency Information Topofbook Message: 78 bytes -/
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
  altLastPx : BitVec 64
  accruedInterestAmt : BitVec 64
  accruedInterestRateP8 : BitVec 64
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
    ++ (encodeUIntLE 8 message.altLastPx
    ++ (encodeUIntLE 8 message.accruedInterestAmt
    ++ (encodeUIntLE 8 message.accruedInterestRateP8
    ++ (encodeUIntLE 4 message.settlDate
    ++ (TransactionCategory.encode message.transactionCategory)))))))))))))))))

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
  let (altLastPx, bytes) ← decodeUIntLE 8 bytes
  let (accruedInterestAmt, bytes) ← decodeUIntLE 8 bytes
  let (accruedInterestRateP8, bytes) ← decodeUIntLE 8 bytes
  let (settlDate, bytes) ← decodeUIntLE 4 bytes
  let (transactionCategory, bytes) ← TransactionCategory.decode bytes
  pure ({ sequenceNumber, securityCode, transactionDateAndTime, marketSegmentId, tradingSessionId, trdMatchId, tradeType, lastPx, lastQty, grossTradeAmt, designation, marketMechanism, algoFlag, altLastPx, accruedInterestAmt, accruedInterestRateP8, settlDate, transactionCategory }, bytes)

@[simp] theorem encode_length (message : TradeMarketPostTransparencyInformationTopofbookMessage) : (encode message).length = 78 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, TradeType.encode_length, Designation.encode_length, MarketMechanism.encode_length, TransactionCategory.encode_length]

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
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [TransactionCategory.decode_encode, some_bind]
  rfl

end TradeMarketPostTransparencyInformationTopofbookMessage

/-- Trade Trade Amendment Or Cancellation Message: 125 bytes -/
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
  altLastPx : BitVec 64
  accruedInterestAmt : BitVec 64
  accruedInterestRateP8 : BitVec 64
  settlDate : BitVec 32
  transactionCategory : TransactionCategory
  lastChangeFlag : BitVec 8
  bencrfptFlag : BencrfptFlag
  tradePriceCondition : TradePriceCondition
  preTradeTransparencyWaiver : PreTradeTransparencyWaiver
  deferralWaiver : DeferralWaiver
  postDeferralPublicationType : PostDeferralPublicationType
  publishDateAndTime : BitVec 64
  tradeDate : BitVec 64
  tradeSessionDate : BitVec 32
  settlDate2 : BitVec 32
  endCash : BitVec 64
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
    ++ (encodeUIntLE 8 message.altLastPx
    ++ (encodeUIntLE 8 message.accruedInterestAmt
    ++ (encodeUIntLE 8 message.accruedInterestRateP8
    ++ (encodeUIntLE 4 message.settlDate
    ++ (TransactionCategory.encode message.transactionCategory
    ++ (encodeUIntLE 1 message.lastChangeFlag
    ++ (BencrfptFlag.encode message.bencrfptFlag
    ++ (TradePriceCondition.encode message.tradePriceCondition
    ++ (PreTradeTransparencyWaiver.encode message.preTradeTransparencyWaiver
    ++ (DeferralWaiver.encode message.deferralWaiver
    ++ (PostDeferralPublicationType.encode message.postDeferralPublicationType
    ++ (encodeUIntLE 8 message.publishDateAndTime
    ++ (encodeUIntLE 8 message.tradeDate
    ++ (encodeUIntLE 4 message.tradeSessionDate
    ++ (encodeUIntLE 4 message.settlDate2
    ++ (encodeUIntLE 8 message.endCash
    ++ (AmendedTradeType.encode message.amendedTradeType
    ++ (encodeUIntLE 4 message.execRefId
    ++ (encodeUIntLE 4 message.amendedTradeDate)))))))))))))))))))))))))))))))

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
  let (altLastPx, bytes) ← decodeUIntLE 8 bytes
  let (accruedInterestAmt, bytes) ← decodeUIntLE 8 bytes
  let (accruedInterestRateP8, bytes) ← decodeUIntLE 8 bytes
  let (settlDate, bytes) ← decodeUIntLE 4 bytes
  let (transactionCategory, bytes) ← TransactionCategory.decode bytes
  let (lastChangeFlag, bytes) ← decodeUIntLE 1 bytes
  let (bencrfptFlag, bytes) ← BencrfptFlag.decode bytes
  let (tradePriceCondition, bytes) ← TradePriceCondition.decode bytes
  let (preTradeTransparencyWaiver, bytes) ← PreTradeTransparencyWaiver.decode bytes
  let (deferralWaiver, bytes) ← DeferralWaiver.decode bytes
  let (postDeferralPublicationType, bytes) ← PostDeferralPublicationType.decode bytes
  let (publishDateAndTime, bytes) ← decodeUIntLE 8 bytes
  let (tradeDate, bytes) ← decodeUIntLE 8 bytes
  let (tradeSessionDate, bytes) ← decodeUIntLE 4 bytes
  let (settlDate2, bytes) ← decodeUIntLE 4 bytes
  let (endCash, bytes) ← decodeUIntLE 8 bytes
  let (amendedTradeType, bytes) ← AmendedTradeType.decode bytes
  let (execRefId, bytes) ← decodeUIntLE 4 bytes
  let (amendedTradeDate, bytes) ← decodeUIntLE 4 bytes
  pure ({ sequenceNumber, securityCode, transactionDateAndTime, marketSegmentId, tradingSessionId, trdMatchId, tradeType, lastPx, lastQty, grossTradeAmt, designation, marketMechanism, algoFlag, altLastPx, accruedInterestAmt, accruedInterestRateP8, settlDate, transactionCategory, lastChangeFlag, bencrfptFlag, tradePriceCondition, preTradeTransparencyWaiver, deferralWaiver, postDeferralPublicationType, publishDateAndTime, tradeDate, tradeSessionDate, settlDate2, endCash, amendedTradeType, execRefId, amendedTradeDate }, bytes)

@[simp] theorem encode_length (message : TradeTradeAmendmentOrCancellationMessage) : (encode message).length = 125 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, TradeType.encode_length, Designation.encode_length, MarketMechanism.encode_length, TransactionCategory.encode_length, BencrfptFlag.encode_length, TradePriceCondition.encode_length, PreTradeTransparencyWaiver.encode_length, DeferralWaiver.encode_length, PostDeferralPublicationType.encode_length, AmendedTradeType.encode_length]

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
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
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
  rw [List.append_assoc, PostDeferralPublicationType.decode_encode, some_bind]
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
  rw [List.append_assoc, AmendedTradeType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end TradeTradeAmendmentOrCancellationMessage

/-- Indication Of Interest Message: 35 bytes -/
structure IndicationOfInterestMessage where
  sequenceNumber : BitVec 32
  securityCode : BitVec 32
  transactionDateAndTime : BitVec 64
  ioiid : BitVec 32
  ioiTransType : IoiTransType
  side : Side
  ioiQty : BitVec 32
  ioiPrice : BitVec 64
  tradingSessionId : BitVec 8
  deriving DecidableEq, Repr

namespace IndicationOfInterestMessage

def encode (message : IndicationOfInterestMessage) : List UInt8 :=
  encodeUIntLE 4 message.sequenceNumber
    ++ (encodeUIntLE 4 message.securityCode
    ++ (encodeUIntLE 8 message.transactionDateAndTime
    ++ (encodeUIntLE 4 message.ioiid
    ++ (IoiTransType.encode message.ioiTransType
    ++ (Side.encode message.side
    ++ (encodeUIntLE 4 message.ioiQty
    ++ (encodeUIntLE 8 message.ioiPrice
    ++ (encodeUIntLE 1 message.tradingSessionId))))))))

def decode (bytes : List UInt8) : Option (IndicationOfInterestMessage × List UInt8) := do
  let (sequenceNumber, bytes) ← decodeUIntLE 4 bytes
  let (securityCode, bytes) ← decodeUIntLE 4 bytes
  let (transactionDateAndTime, bytes) ← decodeUIntLE 8 bytes
  let (ioiid, bytes) ← decodeUIntLE 4 bytes
  let (ioiTransType, bytes) ← IoiTransType.decode bytes
  let (side, bytes) ← Side.decode bytes
  let (ioiQty, bytes) ← decodeUIntLE 4 bytes
  let (ioiPrice, bytes) ← decodeUIntLE 8 bytes
  let (tradingSessionId, bytes) ← decodeUIntLE 1 bytes
  pure ({ sequenceNumber, securityCode, transactionDateAndTime, ioiid, ioiTransType, side, ioiQty, ioiPrice, tradingSessionId }, bytes)

@[simp] theorem encode_length (message : IndicationOfInterestMessage) : (encode message).length = 35 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, IoiTransType.encode_length, Side.encode_length]

theorem encode_length_pos (message : IndicationOfInterestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : IndicationOfInterestMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, IoiTransType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Side.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end IndicationOfInterestMessage

/-- Rfq Market Pre Transparency Information Message: 189 bytes -/
structure RfqMarketPreTransparencyInformationMessage where
  sequenceNumber : BitVec 32
  rfqid : BitVec 32
  tradingSessionId : BitVec 8
  securityCode : BitVec 32
  transactionDateAndTime : BitVec 64
  midBuyPrice : BitVec 64
  midBuyVolume : BitVec 32
  buyRfQsNumber : BitVec 16
  midSellPrice : BitVec 64
  midSellVolume : BitVec 32
  sellRfQsNumber : BitVec 16
  bidOrders1 : BitVec 16
  bidSize1 : BitVec 32
  bidPx1 : BitVec 64
  askOrders1 : BitVec 16
  askSize1 : BitVec 32
  askPx1 : BitVec 64
  bidOrders2 : BitVec 16
  bidSize2 : BitVec 32
  bidPx2 : BitVec 64
  askOrders2 : BitVec 16
  askSize2 : BitVec 32
  askPx2 : BitVec 64
  bidOrders3 : BitVec 16
  bidSize3 : BitVec 32
  bidPx3 : BitVec 64
  askOrders3 : BitVec 16
  askSize3 : BitVec 32
  askPx3 : BitVec 64
  bidOrders4 : BitVec 16
  bidSize4 : BitVec 32
  bidPx4 : BitVec 64
  askOrders4 : BitVec 16
  askSize4 : BitVec 32
  askPx4 : BitVec 64
  bidOrders5 : BitVec 16
  bidSize5 : BitVec 32
  bidPx5 : BitVec 64
  askOrders5 : BitVec 16
  askSize5 : BitVec 32
  askPx5 : BitVec 64
  deriving DecidableEq, Repr

namespace RfqMarketPreTransparencyInformationMessage

def encode (message : RfqMarketPreTransparencyInformationMessage) : List UInt8 :=
  encodeUIntLE 4 message.sequenceNumber
    ++ (encodeUIntLE 4 message.rfqid
    ++ (encodeUIntLE 1 message.tradingSessionId
    ++ (encodeUIntLE 4 message.securityCode
    ++ (encodeUIntLE 8 message.transactionDateAndTime
    ++ (encodeUIntLE 8 message.midBuyPrice
    ++ (encodeUIntLE 4 message.midBuyVolume
    ++ (encodeUIntLE 2 message.buyRfQsNumber
    ++ (encodeUIntLE 8 message.midSellPrice
    ++ (encodeUIntLE 4 message.midSellVolume
    ++ (encodeUIntLE 2 message.sellRfQsNumber
    ++ (encodeUIntLE 2 message.bidOrders1
    ++ (encodeUIntLE 4 message.bidSize1
    ++ (encodeUIntLE 8 message.bidPx1
    ++ (encodeUIntLE 2 message.askOrders1
    ++ (encodeUIntLE 4 message.askSize1
    ++ (encodeUIntLE 8 message.askPx1
    ++ (encodeUIntLE 2 message.bidOrders2
    ++ (encodeUIntLE 4 message.bidSize2
    ++ (encodeUIntLE 8 message.bidPx2
    ++ (encodeUIntLE 2 message.askOrders2
    ++ (encodeUIntLE 4 message.askSize2
    ++ (encodeUIntLE 8 message.askPx2
    ++ (encodeUIntLE 2 message.bidOrders3
    ++ (encodeUIntLE 4 message.bidSize3
    ++ (encodeUIntLE 8 message.bidPx3
    ++ (encodeUIntLE 2 message.askOrders3
    ++ (encodeUIntLE 4 message.askSize3
    ++ (encodeUIntLE 8 message.askPx3
    ++ (encodeUIntLE 2 message.bidOrders4
    ++ (encodeUIntLE 4 message.bidSize4
    ++ (encodeUIntLE 8 message.bidPx4
    ++ (encodeUIntLE 2 message.askOrders4
    ++ (encodeUIntLE 4 message.askSize4
    ++ (encodeUIntLE 8 message.askPx4
    ++ (encodeUIntLE 2 message.bidOrders5
    ++ (encodeUIntLE 4 message.bidSize5
    ++ (encodeUIntLE 8 message.bidPx5
    ++ (encodeUIntLE 2 message.askOrders5
    ++ (encodeUIntLE 4 message.askSize5
    ++ (encodeUIntLE 8 message.askPx5))))))))))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (RfqMarketPreTransparencyInformationMessage × List UInt8) := do
  let (sequenceNumber, bytes) ← decodeUIntLE 4 bytes
  let (rfqid, bytes) ← decodeUIntLE 4 bytes
  let (tradingSessionId, bytes) ← decodeUIntLE 1 bytes
  let (securityCode, bytes) ← decodeUIntLE 4 bytes
  let (transactionDateAndTime, bytes) ← decodeUIntLE 8 bytes
  let (midBuyPrice, bytes) ← decodeUIntLE 8 bytes
  let (midBuyVolume, bytes) ← decodeUIntLE 4 bytes
  let (buyRfQsNumber, bytes) ← decodeUIntLE 2 bytes
  let (midSellPrice, bytes) ← decodeUIntLE 8 bytes
  let (midSellVolume, bytes) ← decodeUIntLE 4 bytes
  let (sellRfQsNumber, bytes) ← decodeUIntLE 2 bytes
  let (bidOrders1, bytes) ← decodeUIntLE 2 bytes
  let (bidSize1, bytes) ← decodeUIntLE 4 bytes
  let (bidPx1, bytes) ← decodeUIntLE 8 bytes
  let (askOrders1, bytes) ← decodeUIntLE 2 bytes
  let (askSize1, bytes) ← decodeUIntLE 4 bytes
  let (askPx1, bytes) ← decodeUIntLE 8 bytes
  let (bidOrders2, bytes) ← decodeUIntLE 2 bytes
  let (bidSize2, bytes) ← decodeUIntLE 4 bytes
  let (bidPx2, bytes) ← decodeUIntLE 8 bytes
  let (askOrders2, bytes) ← decodeUIntLE 2 bytes
  let (askSize2, bytes) ← decodeUIntLE 4 bytes
  let (askPx2, bytes) ← decodeUIntLE 8 bytes
  let (bidOrders3, bytes) ← decodeUIntLE 2 bytes
  let (bidSize3, bytes) ← decodeUIntLE 4 bytes
  let (bidPx3, bytes) ← decodeUIntLE 8 bytes
  let (askOrders3, bytes) ← decodeUIntLE 2 bytes
  let (askSize3, bytes) ← decodeUIntLE 4 bytes
  let (askPx3, bytes) ← decodeUIntLE 8 bytes
  let (bidOrders4, bytes) ← decodeUIntLE 2 bytes
  let (bidSize4, bytes) ← decodeUIntLE 4 bytes
  let (bidPx4, bytes) ← decodeUIntLE 8 bytes
  let (askOrders4, bytes) ← decodeUIntLE 2 bytes
  let (askSize4, bytes) ← decodeUIntLE 4 bytes
  let (askPx4, bytes) ← decodeUIntLE 8 bytes
  let (bidOrders5, bytes) ← decodeUIntLE 2 bytes
  let (bidSize5, bytes) ← decodeUIntLE 4 bytes
  let (bidPx5, bytes) ← decodeUIntLE 8 bytes
  let (askOrders5, bytes) ← decodeUIntLE 2 bytes
  let (askSize5, bytes) ← decodeUIntLE 4 bytes
  let (askPx5, bytes) ← decodeUIntLE 8 bytes
  pure ({ sequenceNumber, rfqid, tradingSessionId, securityCode, transactionDateAndTime, midBuyPrice, midBuyVolume, buyRfQsNumber, midSellPrice, midSellVolume, sellRfQsNumber, bidOrders1, bidSize1, bidPx1, askOrders1, askSize1, askPx1, bidOrders2, bidSize2, bidPx2, askOrders2, askSize2, askPx2, bidOrders3, bidSize3, bidPx3, askOrders3, askSize3, askPx3, bidOrders4, bidSize4, bidPx4, askOrders4, askSize4, askPx4, bidOrders5, bidSize5, bidPx5, askOrders5, askSize5, askPx5 }, bytes)

@[simp] theorem encode_length (message : RfqMarketPreTransparencyInformationMessage) : (encode message).length = 189 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : RfqMarketPreTransparencyInformationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : RfqMarketPreTransparencyInformationMessage) (rest : List UInt8) :
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
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end RfqMarketPreTransparencyInformationMessage

/-- Topofbook Retail Message: 60 bytes -/
structure TopofbookRetailMessage where
  sequenceNumber : BitVec 32
  securityCode : BitVec 32
  transactionDateAndTime : BitVec 64
  bidOrders1 : BitVec 16
  bidSize1 : BitVec 32
  bidPx1 : BitVec 64
  altBidPx1 : BitVec 64
  askOrders1 : BitVec 16
  askSize1 : BitVec 32
  askPx1 : BitVec 64
  altSellPx1 : BitVec 64
  deriving DecidableEq, Repr

namespace TopofbookRetailMessage

def encode (message : TopofbookRetailMessage) : List UInt8 :=
  encodeUIntLE 4 message.sequenceNumber
    ++ (encodeUIntLE 4 message.securityCode
    ++ (encodeUIntLE 8 message.transactionDateAndTime
    ++ (encodeUIntLE 2 message.bidOrders1
    ++ (encodeUIntLE 4 message.bidSize1
    ++ (encodeUIntLE 8 message.bidPx1
    ++ (encodeUIntLE 8 message.altBidPx1
    ++ (encodeUIntLE 2 message.askOrders1
    ++ (encodeUIntLE 4 message.askSize1
    ++ (encodeUIntLE 8 message.askPx1
    ++ (encodeUIntLE 8 message.altSellPx1))))))))))

def decode (bytes : List UInt8) : Option (TopofbookRetailMessage × List UInt8) := do
  let (sequenceNumber, bytes) ← decodeUIntLE 4 bytes
  let (securityCode, bytes) ← decodeUIntLE 4 bytes
  let (transactionDateAndTime, bytes) ← decodeUIntLE 8 bytes
  let (bidOrders1, bytes) ← decodeUIntLE 2 bytes
  let (bidSize1, bytes) ← decodeUIntLE 4 bytes
  let (bidPx1, bytes) ← decodeUIntLE 8 bytes
  let (altBidPx1, bytes) ← decodeUIntLE 8 bytes
  let (askOrders1, bytes) ← decodeUIntLE 2 bytes
  let (askSize1, bytes) ← decodeUIntLE 4 bytes
  let (askPx1, bytes) ← decodeUIntLE 8 bytes
  let (altSellPx1, bytes) ← decodeUIntLE 8 bytes
  pure ({ sequenceNumber, securityCode, transactionDateAndTime, bidOrders1, bidSize1, bidPx1, altBidPx1, askOrders1, askSize1, askPx1, altSellPx1 }, bytes)

@[simp] theorem encode_length (message : TopofbookRetailMessage) : (encode message).length = 60 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : TopofbookRetailMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TopofbookRetailMessage) (rest : List UInt8) :
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
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end TopofbookRetailMessage

/-- Any Payload, selected by Message Type -/
inductive Payload where
  | logonResponseMessage (message : LogonResponseMessage) -- 8
  | logoutResponseMessage (message : LogoutResponseMessage) -- 11
  | heartbeatMessage (message : HeartbeatMessage) -- 48
  | networkStatusMessage (message : NetworkStatusMessage) -- 10
  | tradingSessionStatusMessage (message : TradingSessionStatusMessage) -- 104
  | newsMessage (message : NewsMessage) -- 66
  | securityListCancellationReportMessage (message : SecurityListCancellationReportMessage) -- 120
  | statisticsMessage (message : StatisticsMessage) -- 132
  | securityListMessage (message : SecurityListMessage) -- 121
  | securityListUpdateReportMessage (message : SecurityListUpdateReportMessage) -- 128
  | securityStatusMessage (message : SecurityStatusMessage) -- 102
  | tradeMarketPostTransparencyInformationTopofbookMessage (message : TradeMarketPostTransparencyInformationTopofbookMessage) -- 16
  | tradeTradeAmendmentOrCancellationMessage (message : TradeTradeAmendmentOrCancellationMessage) -- 24
  | indicationOfInterestMessage (message : IndicationOfInterestMessage) -- 54
  | rfqMarketPreTransparencyInformationMessage (message : RfqMarketPreTransparencyInformationMessage) -- 133
  | topofbookRetailMessage (message : TopofbookRetailMessage) -- 145
  deriving DecidableEq, Repr

namespace Payload

/-- The Message Type each message is sent under -/
def tag : Payload → BitVec 8
  | .logonResponseMessage _ => 8
  | .logoutResponseMessage _ => 11
  | .heartbeatMessage _ => 48
  | .networkStatusMessage _ => 10
  | .tradingSessionStatusMessage _ => 104
  | .newsMessage _ => 66
  | .securityListCancellationReportMessage _ => 120
  | .statisticsMessage _ => 132
  | .securityListMessage _ => 121
  | .securityListUpdateReportMessage _ => 128
  | .securityStatusMessage _ => 102
  | .tradeMarketPostTransparencyInformationTopofbookMessage _ => 16
  | .tradeTradeAmendmentOrCancellationMessage _ => 24
  | .indicationOfInterestMessage _ => 54
  | .rfqMarketPreTransparencyInformationMessage _ => 133
  | .topofbookRetailMessage _ => 145

def encode : Payload → List UInt8
  | .logonResponseMessage message => LogonResponseMessage.encode message
  | .logoutResponseMessage message => LogoutResponseMessage.encode message
  | .heartbeatMessage message => HeartbeatMessage.encode message
  | .networkStatusMessage message => NetworkStatusMessage.encode message
  | .tradingSessionStatusMessage message => TradingSessionStatusMessage.encode message
  | .newsMessage message => NewsMessage.encode message
  | .securityListCancellationReportMessage message => SecurityListCancellationReportMessage.encode message
  | .statisticsMessage message => StatisticsMessage.encode message
  | .securityListMessage message => SecurityListMessage.encode message
  | .securityListUpdateReportMessage message => SecurityListUpdateReportMessage.encode message
  | .securityStatusMessage message => SecurityStatusMessage.encode message
  | .tradeMarketPostTransparencyInformationTopofbookMessage message => TradeMarketPostTransparencyInformationTopofbookMessage.encode message
  | .tradeTradeAmendmentOrCancellationMessage message => TradeTradeAmendmentOrCancellationMessage.encode message
  | .indicationOfInterestMessage message => IndicationOfInterestMessage.encode message
  | .rfqMarketPreTransparencyInformationMessage message => RfqMarketPreTransparencyInformationMessage.encode message
  | .topofbookRetailMessage message => TopofbookRetailMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : Payload) : (encode message).length ≤ 450 := by
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
  | tradeMarketPostTransparencyInformationTopofbookMessage inner =>
    simp only [encode, TradeMarketPostTransparencyInformationTopofbookMessage.encode_length]
    omega
  | tradeTradeAmendmentOrCancellationMessage inner =>
    simp only [encode, TradeTradeAmendmentOrCancellationMessage.encode_length]
    omega
  | indicationOfInterestMessage inner =>
    simp only [encode, IndicationOfInterestMessage.encode_length]
    omega
  | rfqMarketPreTransparencyInformationMessage inner =>
    simp only [encode, RfqMarketPreTransparencyInformationMessage.encode_length]
    omega
  | topofbookRetailMessage inner =>
    simp only [encode, TopofbookRetailMessage.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (Payload × List UInt8) :=
  if tag = 8 then (LogonResponseMessage.decode bytes).map fun (message, rest) => (.logonResponseMessage message, rest)
  else if tag = 11 then (LogoutResponseMessage.decode bytes).map fun (message, rest) => (.logoutResponseMessage message, rest)
  else if tag = 48 then (HeartbeatMessage.decode bytes).map fun (message, rest) => (.heartbeatMessage message, rest)
  else if tag = 10 then (NetworkStatusMessage.decode bytes).map fun (message, rest) => (.networkStatusMessage message, rest)
  else if tag = 104 then (TradingSessionStatusMessage.decode bytes).map fun (message, rest) => (.tradingSessionStatusMessage message, rest)
  else if tag = 66 then (NewsMessage.decode bytes).map fun (message, rest) => (.newsMessage message, rest)
  else if tag = 120 then (SecurityListCancellationReportMessage.decode bytes).map fun (message, rest) => (.securityListCancellationReportMessage message, rest)
  else if tag = 132 then (StatisticsMessage.decode bytes).map fun (message, rest) => (.statisticsMessage message, rest)
  else if tag = 121 then (SecurityListMessage.decode bytes).map fun (message, rest) => (.securityListMessage message, rest)
  else if tag = 128 then (SecurityListUpdateReportMessage.decode bytes).map fun (message, rest) => (.securityListUpdateReportMessage message, rest)
  else if tag = 102 then (SecurityStatusMessage.decode bytes).map fun (message, rest) => (.securityStatusMessage message, rest)
  else if tag = 16 then (TradeMarketPostTransparencyInformationTopofbookMessage.decode bytes).map fun (message, rest) => (.tradeMarketPostTransparencyInformationTopofbookMessage message, rest)
  else if tag = 24 then (TradeTradeAmendmentOrCancellationMessage.decode bytes).map fun (message, rest) => (.tradeTradeAmendmentOrCancellationMessage message, rest)
  else if tag = 54 then (IndicationOfInterestMessage.decode bytes).map fun (message, rest) => (.indicationOfInterestMessage message, rest)
  else if tag = 133 then (RfqMarketPreTransparencyInformationMessage.decode bytes).map fun (message, rest) => (.rfqMarketPreTransparencyInformationMessage message, rest)
  else if tag = 145 then (TopofbookRetailMessage.decode bytes).map fun (message, rest) => (.topofbookRetailMessage message, rest)
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
  | tradeMarketPostTransparencyInformationTopofbookMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, TradeMarketPostTransparencyInformationTopofbookMessage.encode_length]
    omega
  | tradeTradeAmendmentOrCancellationMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, TradeTradeAmendmentOrCancellationMessage.encode_length]
    omega
  | indicationOfInterestMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, IndicationOfInterestMessage.encode_length]
    omega
  | rfqMarketPreTransparencyInformationMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, RfqMarketPreTransparencyInformationMessage.encode_length]
    omega
  | topofbookRetailMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, TopofbookRetailMessage.encode_length]
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

end Omi.BmeBmefixedincomeRetailBmegateV16
