import Wire

/-!
# New York Stock Exchange Top Feed v1.3.a

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.NyseArcaoptionsTopfeedXdpV13A

/-- Quote Condition: one byte code -/
def QuoteCondition.codes : List UInt8 :=
  [0x31, 0x32, 0x33, 0x34, 0x35]

inductive QuoteCondition where
  | regularTrading -- Regular Trading
  | rotation -- Rotation
  | tradingHalted -- Trading Halted
  | preopen -- Preopen
  | rotationLegalWidthQuotePending -- Rotation Legal Width Quote Pending
  | unlisted (byte : { byte : UInt8 // byte ∉ QuoteCondition.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace QuoteCondition

def toByte : QuoteCondition → UInt8
  | .regularTrading => 0x31
  | .rotation => 0x32
  | .tradingHalted => 0x33
  | .preopen => 0x34
  | .rotationLegalWidthQuotePending => 0x35
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : QuoteCondition :=
  if byte = 0x31 then .regularTrading
  else if byte = 0x32 then .rotation
  else if byte = 0x33 then .tradingHalted
  else if byte = 0x34 then .preopen
  else .rotationLegalWidthQuotePending

def ofByte (byte : UInt8) : QuoteCondition :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : QuoteCondition) : ofByte value.toByte = value := by
  cases value with
  | regularTrading => decide
  | rotation => decide
  | tradingHalted => decide
  | preopen => decide
  | rotationLegalWidthQuotePending => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : QuoteCondition) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (QuoteCondition × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : QuoteCondition) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : QuoteCondition) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end QuoteCondition

/-- Trade Cond 1: one byte code -/
def TradeCond1.codes : List UInt8 :=
  [0x20, 0x49, 0x52, 0x53]

inductive TradeCond1 where
  | regularTrade -- Regular Trade
  | lateReport -- Late Report
  | floorTrade -- Floor Trade
  | soSweepTrade -- So Sweep Trade
  | unlisted (byte : { byte : UInt8 // byte ∉ TradeCond1.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TradeCond1

def toByte : TradeCond1 → UInt8
  | .regularTrade => 0x20
  | .lateReport => 0x49
  | .floorTrade => 0x52
  | .soSweepTrade => 0x53
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TradeCond1 :=
  if byte = 0x20 then .regularTrade
  else if byte = 0x49 then .lateReport
  else if byte = 0x52 then .floorTrade
  else .soSweepTrade

def ofByte (byte : UInt8) : TradeCond1 :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TradeCond1) : ofByte value.toByte = value := by
  cases value with
  | regularTrade => decide
  | lateReport => decide
  | floorTrade => decide
  | soSweepTrade => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : TradeCond1) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (TradeCond1 × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : TradeCond1) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : TradeCond1) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end TradeCond1

/-- Trade Cond 2: one byte code -/
def TradeCond2.codes : List UInt8 :=
  [0x50, 0x4C]

inductive TradeCond2 where
  | complexTradeWithEquity -- Complex Trade With Equity
  | complexTrade -- Complex Trade
  | unlisted (byte : { byte : UInt8 // byte ∉ TradeCond2.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TradeCond2

def toByte : TradeCond2 → UInt8
  | .complexTradeWithEquity => 0x50
  | .complexTrade => 0x4C
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TradeCond2 :=
  if byte = 0x50 then .complexTradeWithEquity
  else .complexTrade

def ofByte (byte : UInt8) : TradeCond2 :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TradeCond2) : ofByte value.toByte = value := by
  cases value with
  | complexTradeWithEquity => decide
  | complexTrade => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : TradeCond2) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (TradeCond2 × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : TradeCond2) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : TradeCond2) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end TradeCond2

/-- Auction Type: one byte code -/
def AuctionType.codes : List UInt8 :=
  [0x4F, 0x48]

inductive AuctionType where
  | opening -- Opening
  | halt -- Halt
  | unlisted (byte : { byte : UInt8 // byte ∉ AuctionType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace AuctionType

def toByte : AuctionType → UInt8
  | .opening => 0x4F
  | .halt => 0x48
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : AuctionType :=
  if byte = 0x4F then .opening
  else .halt

def ofByte (byte : UInt8) : AuctionType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : AuctionType) : ofByte value.toByte = value := by
  cases value with
  | opening => decide
  | halt => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : AuctionType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (AuctionType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : AuctionType) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : AuctionType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end AuctionType

/-- Imbalance Side: one byte code -/
def ImbalanceSide.codes : List UInt8 :=
  [0x42, 0x53, 0x20]

inductive ImbalanceSide where
  | buy -- Buy
  | sell -- Sell
  | noImbalance -- No Imbalance
  | unlisted (byte : { byte : UInt8 // byte ∉ ImbalanceSide.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ImbalanceSide

def toByte : ImbalanceSide → UInt8
  | .buy => 0x42
  | .sell => 0x53
  | .noImbalance => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ImbalanceSide :=
  if byte = 0x42 then .buy
  else if byte = 0x53 then .sell
  else .noImbalance

def ofByte (byte : UInt8) : ImbalanceSide :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ImbalanceSide) : ofByte value.toByte = value := by
  cases value with
  | buy => decide
  | sell => decide
  | noImbalance => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ImbalanceSide) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ImbalanceSide × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ImbalanceSide) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : ImbalanceSide) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ImbalanceSide

/-- Market Imbalance Side: one byte code -/
def MarketImbalanceSide.codes : List UInt8 :=
  [0x42, 0x53, 0x20]

inductive MarketImbalanceSide where
  | buy -- Buy
  | sell -- Sell
  | noImbalance -- No Imbalance
  | unlisted (byte : { byte : UInt8 // byte ∉ MarketImbalanceSide.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace MarketImbalanceSide

def toByte : MarketImbalanceSide → UInt8
  | .buy => 0x42
  | .sell => 0x53
  | .noImbalance => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : MarketImbalanceSide :=
  if byte = 0x42 then .buy
  else if byte = 0x53 then .sell
  else .noImbalance

def ofByte (byte : UInt8) : MarketImbalanceSide :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : MarketImbalanceSide) : ofByte value.toByte = value := by
  cases value with
  | buy => decide
  | sell => decide
  | noImbalance => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : MarketImbalanceSide) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (MarketImbalanceSide × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : MarketImbalanceSide) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : MarketImbalanceSide) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end MarketImbalanceSide

/-- Side: one byte code -/
def Side.codes : List UInt8 :=
  [0x42, 0x53]

inductive Side where
  | buy -- Buy
  | sell -- Sell
  | unlisted (byte : { byte : UInt8 // byte ∉ Side.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Side

def toByte : Side → UInt8
  | .buy => 0x42
  | .sell => 0x53
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Side :=
  if byte = 0x42 then .buy
  else .sell

def ofByte (byte : UInt8) : Side :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Side) : ofByte value.toByte = value := by
  cases value with
  | buy => decide
  | sell => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Side) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Side × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Side) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : Side) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Side

/-- Capacity: one byte code -/
def Capacity.codes : List UInt8 :=
  [0x20, 0x30, 0x31, 0x32, 0x33, 0x38]

inductive Capacity where
  | notSpecified -- Not Specified
  | customer -- Customer
  | firm -- Firm
  | brokerDealer -- Broker Dealer
  | marketMaker -- Market Maker
  | professionalCustomer -- Professional Customer
  | unlisted (byte : { byte : UInt8 // byte ∉ Capacity.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Capacity

def toByte : Capacity → UInt8
  | .notSpecified => 0x20
  | .customer => 0x30
  | .firm => 0x31
  | .brokerDealer => 0x32
  | .marketMaker => 0x33
  | .professionalCustomer => 0x38
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Capacity :=
  if byte = 0x20 then .notSpecified
  else if byte = 0x30 then .customer
  else if byte = 0x31 then .firm
  else if byte = 0x32 then .brokerDealer
  else if byte = 0x33 then .marketMaker
  else .professionalCustomer

def ofByte (byte : UInt8) : Capacity :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Capacity) : ofByte value.toByte = value := by
  cases value with
  | notSpecified => decide
  | customer => decide
  | firm => decide
  | brokerDealer => decide
  | marketMaker => decide
  | professionalCustomer => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Capacity) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Capacity × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Capacity) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : Capacity) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Capacity

/-- Security Status: one byte code -/
def SecurityStatus.codes : List UInt8 :=
  [0x4C, 0x4E, 0x4F, 0x58, 0x53, 0x55, 0x54, 0x51]

inductive SecurityStatus where
  | lightUpADarkSeries -- Light Up A Dark Series
  | openADarkSeries -- Open A Dark Series
  | open_ -- Open
  | close -- Close
  | halt -- Halt
  | unhalt -- Unhalt
  | unhaltADarkSeries -- Unhalt A Dark Series
  | endOfRfqAuction -- End Of Rfq Auction
  | unlisted (byte : { byte : UInt8 // byte ∉ SecurityStatus.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace SecurityStatus

def toByte : SecurityStatus → UInt8
  | .lightUpADarkSeries => 0x4C
  | .openADarkSeries => 0x4E
  | .open_ => 0x4F
  | .close => 0x58
  | .halt => 0x53
  | .unhalt => 0x55
  | .unhaltADarkSeries => 0x54
  | .endOfRfqAuction => 0x51
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : SecurityStatus :=
  if byte = 0x4C then .lightUpADarkSeries
  else if byte = 0x4E then .openADarkSeries
  else if byte = 0x4F then .open_
  else if byte = 0x58 then .close
  else if byte = 0x53 then .halt
  else if byte = 0x55 then .unhalt
  else if byte = 0x54 then .unhaltADarkSeries
  else .endOfRfqAuction

def ofByte (byte : UInt8) : SecurityStatus :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : SecurityStatus) : ofByte value.toByte = value := by
  cases value with
  | lightUpADarkSeries => decide
  | openADarkSeries => decide
  | open_ => decide
  | close => decide
  | halt => decide
  | unhalt => decide
  | unhaltADarkSeries => decide
  | endOfRfqAuction => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : SecurityStatus) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (SecurityStatus × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : SecurityStatus) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : SecurityStatus) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end SecurityStatus

/-- Exchange Code: one byte code -/
def ExchangeCode.codes : List UInt8 :=
  [0x4E, 0x50, 0x51, 0x41, 0x31, 0x32]

inductive ExchangeCode where
  | nyse -- Nyse
  | nyseArca -- Nyse Arca
  | nasdaq -- Nasdaq
  | nyseMkt -- Nyse Mkt
  | globalOtc -- Global Otc
  | arcaLocalNontapebIndex -- Arca Local Nontapeb Index
  | unlisted (byte : { byte : UInt8 // byte ∉ ExchangeCode.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ExchangeCode

def toByte : ExchangeCode → UInt8
  | .nyse => 0x4E
  | .nyseArca => 0x50
  | .nasdaq => 0x51
  | .nyseMkt => 0x41
  | .globalOtc => 0x31
  | .arcaLocalNontapebIndex => 0x32
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ExchangeCode :=
  if byte = 0x4E then .nyse
  else if byte = 0x50 then .nyseArca
  else if byte = 0x51 then .nasdaq
  else if byte = 0x41 then .nyseMkt
  else if byte = 0x31 then .globalOtc
  else .arcaLocalNontapebIndex

def ofByte (byte : UInt8) : ExchangeCode :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ExchangeCode) : ofByte value.toByte = value := by
  cases value with
  | nyse => decide
  | nyseArca => decide
  | nasdaq => decide
  | nyseMkt => decide
  | globalOtc => decide
  | arcaLocalNontapebIndex => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ExchangeCode) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ExchangeCode × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ExchangeCode) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : ExchangeCode) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ExchangeCode

/-- Security Type: one byte code -/
def SecurityType.codes : List UInt8 :=
  [0x41, 0x43, 0x44, 0x45, 0x46, 0x48, 0x49, 0x4D, 0x4F, 0x50, 0x52, 0x53, 0x54, 0x55, 0x57, 0x58]

inductive SecurityType where
  | adr -- Adr
  | commonStock -- Common Stock
  | debentures -- Debentures
  | etf -- Etf
  | foreign -- Foreign
  | americanDepositoryShares -- American Depository Shares
  | units -- Units
  | miscliquidTrust -- Miscliquid Trust
  | ordinaryShares -- Ordinary Shares
  | preferredStock -- Preferred Stock
  | rights -- Rights
  | sharesOfBeneficiaryInterest -- Shares Of Beneficiary Interest
  | test -- Test
  | units_55 -- Units
  | warrant -- Warrant
  | index -- Index
  | unlisted (byte : { byte : UInt8 // byte ∉ SecurityType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace SecurityType

def toByte : SecurityType → UInt8
  | .adr => 0x41
  | .commonStock => 0x43
  | .debentures => 0x44
  | .etf => 0x45
  | .foreign => 0x46
  | .americanDepositoryShares => 0x48
  | .units => 0x49
  | .miscliquidTrust => 0x4D
  | .ordinaryShares => 0x4F
  | .preferredStock => 0x50
  | .rights => 0x52
  | .sharesOfBeneficiaryInterest => 0x53
  | .test => 0x54
  | .units_55 => 0x55
  | .warrant => 0x57
  | .index => 0x58
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : SecurityType :=
  if byte = 0x41 then .adr
  else if byte = 0x43 then .commonStock
  else if byte = 0x44 then .debentures
  else if byte = 0x45 then .etf
  else if byte = 0x46 then .foreign
  else if byte = 0x48 then .americanDepositoryShares
  else if byte = 0x49 then .units
  else if byte = 0x4D then .miscliquidTrust
  else if byte = 0x4F then .ordinaryShares
  else if byte = 0x50 then .preferredStock
  else if byte = 0x52 then .rights
  else if byte = 0x53 then .sharesOfBeneficiaryInterest
  else if byte = 0x54 then .test
  else if byte = 0x55 then .units_55
  else if byte = 0x57 then .warrant
  else .index

def ofByte (byte : UInt8) : SecurityType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : SecurityType) : ofByte value.toByte = value := by
  cases value with
  | adr => decide
  | commonStock => decide
  | debentures => decide
  | etf => decide
  | foreign => decide
  | americanDepositoryShares => decide
  | units => decide
  | miscliquidTrust => decide
  | ordinaryShares => decide
  | preferredStock => decide
  | rights => decide
  | sharesOfBeneficiaryInterest => decide
  | test => decide
  | units_55 => decide
  | warrant => decide
  | index => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : SecurityType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (SecurityType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : SecurityType) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : SecurityType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end SecurityType

/-- Send Time: 8 bytes -/
structure SendTime where
  seconds : BitVec 32
  nanoseconds : BitVec 32
  deriving DecidableEq, Repr

namespace SendTime

def encode (message : SendTime) : List UInt8 :=
  encodeUIntLE 4 message.seconds
    ++ (encodeUIntLE 4 message.nanoseconds)

def decode (bytes : List UInt8) : Option (SendTime × List UInt8) := do
  let (seconds, bytes) ← decodeUIntLE 4 bytes
  let (nanoseconds, bytes) ← decodeUIntLE 4 bytes
  pure ({ seconds, nanoseconds }, bytes)

@[simp] theorem encode_length (message : SendTime) : (encode message).length = 8 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : SendTime) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SendTime) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end SendTime

/-- Outright Quote Message: 36 bytes -/
structure OutrightQuoteMessage where
  sourceTime : BitVec 32
  sourceTimeNs : BitVec 32
  seriesIndex : BitVec 32
  symbolSeqNum : BitVec 32
  askPrice : BitVec 32
  bidPrice : BitVec 32
  askVolume : BitVec 16
  bidVolume : BitVec 16
  askCustomerVolume : BitVec 16
  bidCustomerVolume : BitVec 16
  quoteCondition : QuoteCondition
  reserved1 : Alpha 1
  reserved2 : Alpha 2
  deriving DecidableEq, Repr

namespace OutrightQuoteMessage

def encode (message : OutrightQuoteMessage) : List UInt8 :=
  encodeUIntLE 4 message.sourceTime
    ++ (encodeUIntLE 4 message.sourceTimeNs
    ++ (encodeUIntLE 4 message.seriesIndex
    ++ (encodeUIntLE 4 message.symbolSeqNum
    ++ (encodeUIntLE 4 message.askPrice
    ++ (encodeUIntLE 4 message.bidPrice
    ++ (encodeUIntLE 2 message.askVolume
    ++ (encodeUIntLE 2 message.bidVolume
    ++ (encodeUIntLE 2 message.askCustomerVolume
    ++ (encodeUIntLE 2 message.bidCustomerVolume
    ++ (QuoteCondition.encode message.quoteCondition
    ++ (Alpha.encode message.reserved1
    ++ (Alpha.encode message.reserved2))))))))))))

def decode (bytes : List UInt8) : Option (OutrightQuoteMessage × List UInt8) := do
  let (sourceTime, bytes) ← decodeUIntLE 4 bytes
  let (sourceTimeNs, bytes) ← decodeUIntLE 4 bytes
  let (seriesIndex, bytes) ← decodeUIntLE 4 bytes
  let (symbolSeqNum, bytes) ← decodeUIntLE 4 bytes
  let (askPrice, bytes) ← decodeUIntLE 4 bytes
  let (bidPrice, bytes) ← decodeUIntLE 4 bytes
  let (askVolume, bytes) ← decodeUIntLE 2 bytes
  let (bidVolume, bytes) ← decodeUIntLE 2 bytes
  let (askCustomerVolume, bytes) ← decodeUIntLE 2 bytes
  let (bidCustomerVolume, bytes) ← decodeUIntLE 2 bytes
  let (quoteCondition, bytes) ← QuoteCondition.decode bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  let (reserved2, bytes) ← Alpha.decode 2 bytes
  pure ({ sourceTime, sourceTimeNs, seriesIndex, symbolSeqNum, askPrice, bidPrice, askVolume, bidVolume, askCustomerVolume, bidCustomerVolume, quoteCondition, reserved1, reserved2 }, bytes)

@[simp] theorem encode_length (message : OutrightQuoteMessage) : (encode message).length = 36 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, QuoteCondition.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : OutrightQuoteMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OutrightQuoteMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, QuoteCondition.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end OutrightQuoteMessage

/-- Outright Trade Message: 32 bytes -/
structure OutrightTradeMessage where
  sourceTime : BitVec 32
  sourceTimeNs : BitVec 32
  seriesIndex : BitVec 32
  symbolSeqNum : BitVec 32
  tradeId : BitVec 32
  price : BitVec 32
  volume4 : BitVec 32
  tradeCond1 : TradeCond1
  tradeCond2 : TradeCond2
  reserved2 : Alpha 2
  deriving DecidableEq, Repr

namespace OutrightTradeMessage

def encode (message : OutrightTradeMessage) : List UInt8 :=
  encodeUIntLE 4 message.sourceTime
    ++ (encodeUIntLE 4 message.sourceTimeNs
    ++ (encodeUIntLE 4 message.seriesIndex
    ++ (encodeUIntLE 4 message.symbolSeqNum
    ++ (encodeUIntLE 4 message.tradeId
    ++ (encodeUIntLE 4 message.price
    ++ (encodeUIntLE 4 message.volume4
    ++ (TradeCond1.encode message.tradeCond1
    ++ (TradeCond2.encode message.tradeCond2
    ++ (Alpha.encode message.reserved2)))))))))

def decode (bytes : List UInt8) : Option (OutrightTradeMessage × List UInt8) := do
  let (sourceTime, bytes) ← decodeUIntLE 4 bytes
  let (sourceTimeNs, bytes) ← decodeUIntLE 4 bytes
  let (seriesIndex, bytes) ← decodeUIntLE 4 bytes
  let (symbolSeqNum, bytes) ← decodeUIntLE 4 bytes
  let (tradeId, bytes) ← decodeUIntLE 4 bytes
  let (price, bytes) ← decodeUIntLE 4 bytes
  let (volume4, bytes) ← decodeUIntLE 4 bytes
  let (tradeCond1, bytes) ← TradeCond1.decode bytes
  let (tradeCond2, bytes) ← TradeCond2.decode bytes
  let (reserved2, bytes) ← Alpha.decode 2 bytes
  pure ({ sourceTime, sourceTimeNs, seriesIndex, symbolSeqNum, tradeId, price, volume4, tradeCond1, tradeCond2, reserved2 }, bytes)

@[simp] theorem encode_length (message : OutrightTradeMessage) : (encode message).length = 32 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, TradeCond1.encode_length, TradeCond2.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : OutrightTradeMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OutrightTradeMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, TradeCond1.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TradeCond2.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end OutrightTradeMessage

/-- Outright Trade Cancel Message: 20 bytes -/
structure OutrightTradeCancelMessage where
  sourceTime : BitVec 32
  sourceTimeNs : BitVec 32
  seriesIndex : BitVec 32
  symbolSeqNum : BitVec 32
  originalTradeId : BitVec 32
  deriving DecidableEq, Repr

namespace OutrightTradeCancelMessage

def encode (message : OutrightTradeCancelMessage) : List UInt8 :=
  encodeUIntLE 4 message.sourceTime
    ++ (encodeUIntLE 4 message.sourceTimeNs
    ++ (encodeUIntLE 4 message.seriesIndex
    ++ (encodeUIntLE 4 message.symbolSeqNum
    ++ (encodeUIntLE 4 message.originalTradeId))))

def decode (bytes : List UInt8) : Option (OutrightTradeCancelMessage × List UInt8) := do
  let (sourceTime, bytes) ← decodeUIntLE 4 bytes
  let (sourceTimeNs, bytes) ← decodeUIntLE 4 bytes
  let (seriesIndex, bytes) ← decodeUIntLE 4 bytes
  let (symbolSeqNum, bytes) ← decodeUIntLE 4 bytes
  let (originalTradeId, bytes) ← decodeUIntLE 4 bytes
  pure ({ sourceTime, sourceTimeNs, seriesIndex, symbolSeqNum, originalTradeId }, bytes)

@[simp] theorem encode_length (message : OutrightTradeCancelMessage) : (encode message).length = 20 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : OutrightTradeCancelMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OutrightTradeCancelMessage) (rest : List UInt8) :
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

end OutrightTradeCancelMessage

/-- Outright Trade Correction Message: 36 bytes -/
structure OutrightTradeCorrectionMessage where
  sourceTime : BitVec 32
  sourceTimeNs : BitVec 32
  seriesIndex : BitVec 32
  symbolSeqNum : BitVec 32
  originalTradeId : BitVec 32
  tradeId : BitVec 32
  price : BitVec 32
  volume4 : BitVec 32
  tradeCond1 : TradeCond1
  tradeCond2 : TradeCond2
  reserved2 : Alpha 2
  deriving DecidableEq, Repr

namespace OutrightTradeCorrectionMessage

def encode (message : OutrightTradeCorrectionMessage) : List UInt8 :=
  encodeUIntLE 4 message.sourceTime
    ++ (encodeUIntLE 4 message.sourceTimeNs
    ++ (encodeUIntLE 4 message.seriesIndex
    ++ (encodeUIntLE 4 message.symbolSeqNum
    ++ (encodeUIntLE 4 message.originalTradeId
    ++ (encodeUIntLE 4 message.tradeId
    ++ (encodeUIntLE 4 message.price
    ++ (encodeUIntLE 4 message.volume4
    ++ (TradeCond1.encode message.tradeCond1
    ++ (TradeCond2.encode message.tradeCond2
    ++ (Alpha.encode message.reserved2))))))))))

def decode (bytes : List UInt8) : Option (OutrightTradeCorrectionMessage × List UInt8) := do
  let (sourceTime, bytes) ← decodeUIntLE 4 bytes
  let (sourceTimeNs, bytes) ← decodeUIntLE 4 bytes
  let (seriesIndex, bytes) ← decodeUIntLE 4 bytes
  let (symbolSeqNum, bytes) ← decodeUIntLE 4 bytes
  let (originalTradeId, bytes) ← decodeUIntLE 4 bytes
  let (tradeId, bytes) ← decodeUIntLE 4 bytes
  let (price, bytes) ← decodeUIntLE 4 bytes
  let (volume4, bytes) ← decodeUIntLE 4 bytes
  let (tradeCond1, bytes) ← TradeCond1.decode bytes
  let (tradeCond2, bytes) ← TradeCond2.decode bytes
  let (reserved2, bytes) ← Alpha.decode 2 bytes
  pure ({ sourceTime, sourceTimeNs, seriesIndex, symbolSeqNum, originalTradeId, tradeId, price, volume4, tradeCond1, tradeCond2, reserved2 }, bytes)

@[simp] theorem encode_length (message : OutrightTradeCorrectionMessage) : (encode message).length = 36 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, TradeCond1.encode_length, TradeCond2.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : OutrightTradeCorrectionMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OutrightTradeCorrectionMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, TradeCond1.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TradeCond2.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end OutrightTradeCorrectionMessage

/-- Outright Imbalance Message: 32 bytes -/
structure OutrightImbalanceMessage where
  sourceTime : BitVec 32
  sourceTimeNs : BitVec 32
  seriesIndex : BitVec 32
  symbolSeqNum : BitVec 32
  referencePrice : BitVec 32
  pairedQty : BitVec 16
  totalImbalanceQty : BitVec 16
  marketImbalanceQty : BitVec 16
  auctionType : AuctionType
  imbalanceSide : ImbalanceSide
  marketImbalanceSide : MarketImbalanceSide
  reserved3 : Alpha 3
  deriving DecidableEq, Repr

namespace OutrightImbalanceMessage

def encode (message : OutrightImbalanceMessage) : List UInt8 :=
  encodeUIntLE 4 message.sourceTime
    ++ (encodeUIntLE 4 message.sourceTimeNs
    ++ (encodeUIntLE 4 message.seriesIndex
    ++ (encodeUIntLE 4 message.symbolSeqNum
    ++ (encodeUIntLE 4 message.referencePrice
    ++ (encodeUIntLE 2 message.pairedQty
    ++ (encodeUIntLE 2 message.totalImbalanceQty
    ++ (encodeUIntLE 2 message.marketImbalanceQty
    ++ (AuctionType.encode message.auctionType
    ++ (ImbalanceSide.encode message.imbalanceSide
    ++ (MarketImbalanceSide.encode message.marketImbalanceSide
    ++ (Alpha.encode message.reserved3)))))))))))

def decode (bytes : List UInt8) : Option (OutrightImbalanceMessage × List UInt8) := do
  let (sourceTime, bytes) ← decodeUIntLE 4 bytes
  let (sourceTimeNs, bytes) ← decodeUIntLE 4 bytes
  let (seriesIndex, bytes) ← decodeUIntLE 4 bytes
  let (symbolSeqNum, bytes) ← decodeUIntLE 4 bytes
  let (referencePrice, bytes) ← decodeUIntLE 4 bytes
  let (pairedQty, bytes) ← decodeUIntLE 2 bytes
  let (totalImbalanceQty, bytes) ← decodeUIntLE 2 bytes
  let (marketImbalanceQty, bytes) ← decodeUIntLE 2 bytes
  let (auctionType, bytes) ← AuctionType.decode bytes
  let (imbalanceSide, bytes) ← ImbalanceSide.decode bytes
  let (marketImbalanceSide, bytes) ← MarketImbalanceSide.decode bytes
  let (reserved3, bytes) ← Alpha.decode 3 bytes
  pure ({ sourceTime, sourceTimeNs, seriesIndex, symbolSeqNum, referencePrice, pairedQty, totalImbalanceQty, marketImbalanceQty, auctionType, imbalanceSide, marketImbalanceSide, reserved3 }, bytes)

@[simp] theorem encode_length (message : OutrightImbalanceMessage) : (encode message).length = 32 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, AuctionType.encode_length, ImbalanceSide.encode_length, MarketImbalanceSide.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : OutrightImbalanceMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OutrightImbalanceMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, AuctionType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ImbalanceSide.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, MarketImbalanceSide.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end OutrightImbalanceMessage

/-- Outright Crossing Rfq Message: 24 bytes -/
structure OutrightCrossingRfqMessage where
  sourceTime : BitVec 32
  sourceNs : BitVec 32
  seriesIndex : BitVec 32
  symbolSeqNum : BitVec 32
  side : Side
  reserved1 : Alpha 1
  volume2 : BitVec 16
  price : BitVec 32
  deriving DecidableEq, Repr

namespace OutrightCrossingRfqMessage

def encode (message : OutrightCrossingRfqMessage) : List UInt8 :=
  encodeUIntLE 4 message.sourceTime
    ++ (encodeUIntLE 4 message.sourceNs
    ++ (encodeUIntLE 4 message.seriesIndex
    ++ (encodeUIntLE 4 message.symbolSeqNum
    ++ (Side.encode message.side
    ++ (Alpha.encode message.reserved1
    ++ (encodeUIntLE 2 message.volume2
    ++ (encodeUIntLE 4 message.price)))))))

def decode (bytes : List UInt8) : Option (OutrightCrossingRfqMessage × List UInt8) := do
  let (sourceTime, bytes) ← decodeUIntLE 4 bytes
  let (sourceNs, bytes) ← decodeUIntLE 4 bytes
  let (seriesIndex, bytes) ← decodeUIntLE 4 bytes
  let (symbolSeqNum, bytes) ← decodeUIntLE 4 bytes
  let (side, bytes) ← Side.decode bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  let (volume2, bytes) ← decodeUIntLE 2 bytes
  let (price, bytes) ← decodeUIntLE 4 bytes
  pure ({ sourceTime, sourceNs, seriesIndex, symbolSeqNum, side, reserved1, volume2, price }, bytes)

@[simp] theorem encode_length (message : OutrightCrossingRfqMessage) : (encode message).length = 24 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Side.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : OutrightCrossingRfqMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OutrightCrossingRfqMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, Side.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end OutrightCrossingRfqMessage

/-- Outright Bold Rfq Message: 28 bytes -/
structure OutrightBoldRfqMessage where
  sourceTime : BitVec 32
  sourceNs : BitVec 32
  seriesIndex : BitVec 32
  symbolSeqNum : BitVec 32
  side : Side
  capacity : Capacity
  contracts : BitVec 16
  price : BitVec 32
  participant : Alpha 4
  deriving DecidableEq, Repr

namespace OutrightBoldRfqMessage

def encode (message : OutrightBoldRfqMessage) : List UInt8 :=
  encodeUIntLE 4 message.sourceTime
    ++ (encodeUIntLE 4 message.sourceNs
    ++ (encodeUIntLE 4 message.seriesIndex
    ++ (encodeUIntLE 4 message.symbolSeqNum
    ++ (Side.encode message.side
    ++ (Capacity.encode message.capacity
    ++ (encodeUIntLE 2 message.contracts
    ++ (encodeUIntLE 4 message.price
    ++ (Alpha.encode message.participant))))))))

def decode (bytes : List UInt8) : Option (OutrightBoldRfqMessage × List UInt8) := do
  let (sourceTime, bytes) ← decodeUIntLE 4 bytes
  let (sourceNs, bytes) ← decodeUIntLE 4 bytes
  let (seriesIndex, bytes) ← decodeUIntLE 4 bytes
  let (symbolSeqNum, bytes) ← decodeUIntLE 4 bytes
  let (side, bytes) ← Side.decode bytes
  let (capacity, bytes) ← Capacity.decode bytes
  let (contracts, bytes) ← decodeUIntLE 2 bytes
  let (price, bytes) ← decodeUIntLE 4 bytes
  let (participant, bytes) ← Alpha.decode 4 bytes
  pure ({ sourceTime, sourceNs, seriesIndex, symbolSeqNum, side, capacity, contracts, price, participant }, bytes)

@[simp] theorem encode_length (message : OutrightBoldRfqMessage) : (encode message).length = 28 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Side.encode_length, Capacity.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : OutrightBoldRfqMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OutrightBoldRfqMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, Side.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Capacity.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end OutrightBoldRfqMessage

/-- Outright Summary Message: 36 bytes -/
structure OutrightSummaryMessage where
  sourceTime : BitVec 32
  sourceTimeNs : BitVec 32
  seriesIndex : BitVec 32
  symbolSeqNum : BitVec 32
  highPrice : BitVec 32
  lowPrice : BitVec 32
  open_ : BitVec 32
  close : BitVec 32
  totalVolume : BitVec 32
  deriving DecidableEq, Repr

namespace OutrightSummaryMessage

def encode (message : OutrightSummaryMessage) : List UInt8 :=
  encodeUIntLE 4 message.sourceTime
    ++ (encodeUIntLE 4 message.sourceTimeNs
    ++ (encodeUIntLE 4 message.seriesIndex
    ++ (encodeUIntLE 4 message.symbolSeqNum
    ++ (encodeUIntLE 4 message.highPrice
    ++ (encodeUIntLE 4 message.lowPrice
    ++ (encodeUIntLE 4 message.open_
    ++ (encodeUIntLE 4 message.close
    ++ (encodeUIntLE 4 message.totalVolume))))))))

def decode (bytes : List UInt8) : Option (OutrightSummaryMessage × List UInt8) := do
  let (sourceTime, bytes) ← decodeUIntLE 4 bytes
  let (sourceTimeNs, bytes) ← decodeUIntLE 4 bytes
  let (seriesIndex, bytes) ← decodeUIntLE 4 bytes
  let (symbolSeqNum, bytes) ← decodeUIntLE 4 bytes
  let (highPrice, bytes) ← decodeUIntLE 4 bytes
  let (lowPrice, bytes) ← decodeUIntLE 4 bytes
  let (open_, bytes) ← decodeUIntLE 4 bytes
  let (close, bytes) ← decodeUIntLE 4 bytes
  let (totalVolume, bytes) ← decodeUIntLE 4 bytes
  pure ({ sourceTime, sourceTimeNs, seriesIndex, symbolSeqNum, highPrice, lowPrice, open_, close, totalVolume }, bytes)

@[simp] theorem encode_length (message : OutrightSummaryMessage) : (encode message).length = 36 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : OutrightSummaryMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OutrightSummaryMessage) (rest : List UInt8) :
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

end OutrightSummaryMessage

/-- Underlying Status Message: 20 bytes -/
structure UnderlyingStatusMessage where
  sourceTime : BitVec 32
  sourceTimeNs : BitVec 32
  underlyingIndex : BitVec 32
  underlyingSeqNum : BitVec 32
  securityStatus : SecurityStatus
  haltCondition : Alpha 1
  reserved2 : Alpha 2
  deriving DecidableEq, Repr

namespace UnderlyingStatusMessage

def encode (message : UnderlyingStatusMessage) : List UInt8 :=
  encodeUIntLE 4 message.sourceTime
    ++ (encodeUIntLE 4 message.sourceTimeNs
    ++ (encodeUIntLE 4 message.underlyingIndex
    ++ (encodeUIntLE 4 message.underlyingSeqNum
    ++ (SecurityStatus.encode message.securityStatus
    ++ (Alpha.encode message.haltCondition
    ++ (Alpha.encode message.reserved2))))))

def decode (bytes : List UInt8) : Option (UnderlyingStatusMessage × List UInt8) := do
  let (sourceTime, bytes) ← decodeUIntLE 4 bytes
  let (sourceTimeNs, bytes) ← decodeUIntLE 4 bytes
  let (underlyingIndex, bytes) ← decodeUIntLE 4 bytes
  let (underlyingSeqNum, bytes) ← decodeUIntLE 4 bytes
  let (securityStatus, bytes) ← SecurityStatus.decode bytes
  let (haltCondition, bytes) ← Alpha.decode 1 bytes
  let (reserved2, bytes) ← Alpha.decode 2 bytes
  pure ({ sourceTime, sourceTimeNs, underlyingIndex, underlyingSeqNum, securityStatus, haltCondition, reserved2 }, bytes)

@[simp] theorem encode_length (message : UnderlyingStatusMessage) : (encode message).length = 20 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, SecurityStatus.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : UnderlyingStatusMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : UnderlyingStatusMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, SecurityStatus.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end UnderlyingStatusMessage

/-- Outright Series Status Message: 20 bytes -/
structure OutrightSeriesStatusMessage where
  sourceTime : BitVec 32
  sourceTimeNs : BitVec 32
  seriesIndex : BitVec 32
  symbolSeqNum : BitVec 32
  securityStatus : SecurityStatus
  haltCondition : Alpha 1
  reserved2 : Alpha 2
  deriving DecidableEq, Repr

namespace OutrightSeriesStatusMessage

def encode (message : OutrightSeriesStatusMessage) : List UInt8 :=
  encodeUIntLE 4 message.sourceTime
    ++ (encodeUIntLE 4 message.sourceTimeNs
    ++ (encodeUIntLE 4 message.seriesIndex
    ++ (encodeUIntLE 4 message.symbolSeqNum
    ++ (SecurityStatus.encode message.securityStatus
    ++ (Alpha.encode message.haltCondition
    ++ (Alpha.encode message.reserved2))))))

def decode (bytes : List UInt8) : Option (OutrightSeriesStatusMessage × List UInt8) := do
  let (sourceTime, bytes) ← decodeUIntLE 4 bytes
  let (sourceTimeNs, bytes) ← decodeUIntLE 4 bytes
  let (seriesIndex, bytes) ← decodeUIntLE 4 bytes
  let (symbolSeqNum, bytes) ← decodeUIntLE 4 bytes
  let (securityStatus, bytes) ← SecurityStatus.decode bytes
  let (haltCondition, bytes) ← Alpha.decode 1 bytes
  let (reserved2, bytes) ← Alpha.decode 2 bytes
  pure ({ sourceTime, sourceTimeNs, seriesIndex, symbolSeqNum, securityStatus, haltCondition, reserved2 }, bytes)

@[simp] theorem encode_length (message : OutrightSeriesStatusMessage) : (encode message).length = 20 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, SecurityStatus.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : OutrightSeriesStatusMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OutrightSeriesStatusMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, SecurityStatus.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end OutrightSeriesStatusMessage

/-- Refresh Outright Quote Message: 36 bytes -/
structure RefreshOutrightQuoteMessage where
  sourceTime : BitVec 32
  sourceTimeNs : BitVec 32
  seriesIndex : BitVec 32
  symbolSeqNum : BitVec 32
  askPrice : BitVec 32
  bidPrice : BitVec 32
  askVolume : BitVec 16
  bidVolume : BitVec 16
  askCustomerVolume : BitVec 16
  bidCustomerVolume : BitVec 16
  quoteCondition : QuoteCondition
  reserved1 : Alpha 1
  reserved2 : Alpha 2
  deriving DecidableEq, Repr

namespace RefreshOutrightQuoteMessage

def encode (message : RefreshOutrightQuoteMessage) : List UInt8 :=
  encodeUIntLE 4 message.sourceTime
    ++ (encodeUIntLE 4 message.sourceTimeNs
    ++ (encodeUIntLE 4 message.seriesIndex
    ++ (encodeUIntLE 4 message.symbolSeqNum
    ++ (encodeUIntLE 4 message.askPrice
    ++ (encodeUIntLE 4 message.bidPrice
    ++ (encodeUIntLE 2 message.askVolume
    ++ (encodeUIntLE 2 message.bidVolume
    ++ (encodeUIntLE 2 message.askCustomerVolume
    ++ (encodeUIntLE 2 message.bidCustomerVolume
    ++ (QuoteCondition.encode message.quoteCondition
    ++ (Alpha.encode message.reserved1
    ++ (Alpha.encode message.reserved2))))))))))))

def decode (bytes : List UInt8) : Option (RefreshOutrightQuoteMessage × List UInt8) := do
  let (sourceTime, bytes) ← decodeUIntLE 4 bytes
  let (sourceTimeNs, bytes) ← decodeUIntLE 4 bytes
  let (seriesIndex, bytes) ← decodeUIntLE 4 bytes
  let (symbolSeqNum, bytes) ← decodeUIntLE 4 bytes
  let (askPrice, bytes) ← decodeUIntLE 4 bytes
  let (bidPrice, bytes) ← decodeUIntLE 4 bytes
  let (askVolume, bytes) ← decodeUIntLE 2 bytes
  let (bidVolume, bytes) ← decodeUIntLE 2 bytes
  let (askCustomerVolume, bytes) ← decodeUIntLE 2 bytes
  let (bidCustomerVolume, bytes) ← decodeUIntLE 2 bytes
  let (quoteCondition, bytes) ← QuoteCondition.decode bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  let (reserved2, bytes) ← Alpha.decode 2 bytes
  pure ({ sourceTime, sourceTimeNs, seriesIndex, symbolSeqNum, askPrice, bidPrice, askVolume, bidVolume, askCustomerVolume, bidCustomerVolume, quoteCondition, reserved1, reserved2 }, bytes)

@[simp] theorem encode_length (message : RefreshOutrightQuoteMessage) : (encode message).length = 36 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, QuoteCondition.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : RefreshOutrightQuoteMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : RefreshOutrightQuoteMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, QuoteCondition.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end RefreshOutrightQuoteMessage

/-- Refresh Outright Trade Message: 32 bytes -/
structure RefreshOutrightTradeMessage where
  sourceTime : BitVec 32
  sourceTimeNs : BitVec 32
  seriesIndex : BitVec 32
  symbolSeqNum : BitVec 32
  tradeId : BitVec 32
  price : BitVec 32
  volume4 : BitVec 32
  tradeCond1 : TradeCond1
  tradeCond2 : TradeCond2
  reserved2 : Alpha 2
  deriving DecidableEq, Repr

namespace RefreshOutrightTradeMessage

def encode (message : RefreshOutrightTradeMessage) : List UInt8 :=
  encodeUIntLE 4 message.sourceTime
    ++ (encodeUIntLE 4 message.sourceTimeNs
    ++ (encodeUIntLE 4 message.seriesIndex
    ++ (encodeUIntLE 4 message.symbolSeqNum
    ++ (encodeUIntLE 4 message.tradeId
    ++ (encodeUIntLE 4 message.price
    ++ (encodeUIntLE 4 message.volume4
    ++ (TradeCond1.encode message.tradeCond1
    ++ (TradeCond2.encode message.tradeCond2
    ++ (Alpha.encode message.reserved2)))))))))

def decode (bytes : List UInt8) : Option (RefreshOutrightTradeMessage × List UInt8) := do
  let (sourceTime, bytes) ← decodeUIntLE 4 bytes
  let (sourceTimeNs, bytes) ← decodeUIntLE 4 bytes
  let (seriesIndex, bytes) ← decodeUIntLE 4 bytes
  let (symbolSeqNum, bytes) ← decodeUIntLE 4 bytes
  let (tradeId, bytes) ← decodeUIntLE 4 bytes
  let (price, bytes) ← decodeUIntLE 4 bytes
  let (volume4, bytes) ← decodeUIntLE 4 bytes
  let (tradeCond1, bytes) ← TradeCond1.decode bytes
  let (tradeCond2, bytes) ← TradeCond2.decode bytes
  let (reserved2, bytes) ← Alpha.decode 2 bytes
  pure ({ sourceTime, sourceTimeNs, seriesIndex, symbolSeqNum, tradeId, price, volume4, tradeCond1, tradeCond2, reserved2 }, bytes)

@[simp] theorem encode_length (message : RefreshOutrightTradeMessage) : (encode message).length = 32 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, TradeCond1.encode_length, TradeCond2.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : RefreshOutrightTradeMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : RefreshOutrightTradeMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, TradeCond1.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TradeCond2.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end RefreshOutrightTradeMessage

/-- Refresh Outright Imbalance Message: 32 bytes -/
structure RefreshOutrightImbalanceMessage where
  sourceTime : BitVec 32
  sourceTimeNs : BitVec 32
  seriesIndex : BitVec 32
  symbolSeqNum : BitVec 32
  referencePrice : BitVec 32
  pairedQty : BitVec 16
  totalImbalanceQty : BitVec 16
  marketImbalanceQty : BitVec 16
  auctionType : AuctionType
  imbalanceSide : ImbalanceSide
  marketImbalanceSide : MarketImbalanceSide
  reserved3 : Alpha 3
  deriving DecidableEq, Repr

namespace RefreshOutrightImbalanceMessage

def encode (message : RefreshOutrightImbalanceMessage) : List UInt8 :=
  encodeUIntLE 4 message.sourceTime
    ++ (encodeUIntLE 4 message.sourceTimeNs
    ++ (encodeUIntLE 4 message.seriesIndex
    ++ (encodeUIntLE 4 message.symbolSeqNum
    ++ (encodeUIntLE 4 message.referencePrice
    ++ (encodeUIntLE 2 message.pairedQty
    ++ (encodeUIntLE 2 message.totalImbalanceQty
    ++ (encodeUIntLE 2 message.marketImbalanceQty
    ++ (AuctionType.encode message.auctionType
    ++ (ImbalanceSide.encode message.imbalanceSide
    ++ (MarketImbalanceSide.encode message.marketImbalanceSide
    ++ (Alpha.encode message.reserved3)))))))))))

def decode (bytes : List UInt8) : Option (RefreshOutrightImbalanceMessage × List UInt8) := do
  let (sourceTime, bytes) ← decodeUIntLE 4 bytes
  let (sourceTimeNs, bytes) ← decodeUIntLE 4 bytes
  let (seriesIndex, bytes) ← decodeUIntLE 4 bytes
  let (symbolSeqNum, bytes) ← decodeUIntLE 4 bytes
  let (referencePrice, bytes) ← decodeUIntLE 4 bytes
  let (pairedQty, bytes) ← decodeUIntLE 2 bytes
  let (totalImbalanceQty, bytes) ← decodeUIntLE 2 bytes
  let (marketImbalanceQty, bytes) ← decodeUIntLE 2 bytes
  let (auctionType, bytes) ← AuctionType.decode bytes
  let (imbalanceSide, bytes) ← ImbalanceSide.decode bytes
  let (marketImbalanceSide, bytes) ← MarketImbalanceSide.decode bytes
  let (reserved3, bytes) ← Alpha.decode 3 bytes
  pure ({ sourceTime, sourceTimeNs, seriesIndex, symbolSeqNum, referencePrice, pairedQty, totalImbalanceQty, marketImbalanceQty, auctionType, imbalanceSide, marketImbalanceSide, reserved3 }, bytes)

@[simp] theorem encode_length (message : RefreshOutrightImbalanceMessage) : (encode message).length = 32 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, AuctionType.encode_length, ImbalanceSide.encode_length, MarketImbalanceSide.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : RefreshOutrightImbalanceMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : RefreshOutrightImbalanceMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, AuctionType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ImbalanceSide.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, MarketImbalanceSide.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end RefreshOutrightImbalanceMessage

/-- Underlying Index Mapping Message: 24 bytes -/
structure UnderlyingIndexMappingMessage where
  underlyingIndex : BitVec 32
  underlyingSymbol : Alpha 11
  channelId : BitVec 8
  marketId : BitVec 16
  systemId : BitVec 8
  exchangeCode : ExchangeCode
  priceScaleCode : BitVec 8
  securityType : SecurityType
  priceResolution : BitVec 8
  reserved1 : Alpha 1
  deriving DecidableEq, Repr

namespace UnderlyingIndexMappingMessage

def encode (message : UnderlyingIndexMappingMessage) : List UInt8 :=
  encodeUIntLE 4 message.underlyingIndex
    ++ (Alpha.encode message.underlyingSymbol
    ++ (encodeUIntLE 1 message.channelId
    ++ (encodeUIntLE 2 message.marketId
    ++ (encodeUIntLE 1 message.systemId
    ++ (ExchangeCode.encode message.exchangeCode
    ++ (encodeUIntLE 1 message.priceScaleCode
    ++ (SecurityType.encode message.securityType
    ++ (encodeUIntLE 1 message.priceResolution
    ++ (Alpha.encode message.reserved1)))))))))

def decode (bytes : List UInt8) : Option (UnderlyingIndexMappingMessage × List UInt8) := do
  let (underlyingIndex, bytes) ← decodeUIntLE 4 bytes
  let (underlyingSymbol, bytes) ← Alpha.decode 11 bytes
  let (channelId, bytes) ← decodeUIntLE 1 bytes
  let (marketId, bytes) ← decodeUIntLE 2 bytes
  let (systemId, bytes) ← decodeUIntLE 1 bytes
  let (exchangeCode, bytes) ← ExchangeCode.decode bytes
  let (priceScaleCode, bytes) ← decodeUIntLE 1 bytes
  let (securityType, bytes) ← SecurityType.decode bytes
  let (priceResolution, bytes) ← decodeUIntLE 1 bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  pure ({ underlyingIndex, underlyingSymbol, channelId, marketId, systemId, exchangeCode, priceScaleCode, securityType, priceResolution, reserved1 }, bytes)

@[simp] theorem encode_length (message : UnderlyingIndexMappingMessage) : (encode message).length = 24 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, ExchangeCode.encode_length, SecurityType.encode_length]

theorem encode_length_pos (message : UnderlyingIndexMappingMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : UnderlyingIndexMappingMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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
  rw [List.append_assoc, ExchangeCode.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, SecurityType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end UnderlyingIndexMappingMessage

/-- Series Index Mapping Message: 56 bytes -/
structure SeriesIndexMappingMessage where
  seriesIndex : BitVec 32
  channelId : BitVec 8
  reservedA1 : Alpha 1
  marketId : BitVec 16
  systemId : BitVec 8
  reservedB1 : Alpha 1
  streamId : BitVec 16
  underlyingIndex : BitVec 32
  contractMultiplier : BitVec 16
  maturityDate : Alpha 6
  putOrCall : BitVec 8
  strikePrice : Alpha 10
  priceScaleCode : BitVec 8
  underlyingSymbol : Alpha 11
  optionSymbolRoot : Alpha 5
  groupId : BitVec 32
  deriving DecidableEq, Repr

namespace SeriesIndexMappingMessage

def encode (message : SeriesIndexMappingMessage) : List UInt8 :=
  encodeUIntLE 4 message.seriesIndex
    ++ (encodeUIntLE 1 message.channelId
    ++ (Alpha.encode message.reservedA1
    ++ (encodeUIntLE 2 message.marketId
    ++ (encodeUIntLE 1 message.systemId
    ++ (Alpha.encode message.reservedB1
    ++ (encodeUIntLE 2 message.streamId
    ++ (encodeUIntLE 4 message.underlyingIndex
    ++ (encodeUIntLE 2 message.contractMultiplier
    ++ (Alpha.encode message.maturityDate
    ++ (encodeUIntLE 1 message.putOrCall
    ++ (Alpha.encode message.strikePrice
    ++ (encodeUIntLE 1 message.priceScaleCode
    ++ (Alpha.encode message.underlyingSymbol
    ++ (Alpha.encode message.optionSymbolRoot
    ++ (encodeUIntLE 4 message.groupId)))))))))))))))

def decode (bytes : List UInt8) : Option (SeriesIndexMappingMessage × List UInt8) := do
  let (seriesIndex, bytes) ← decodeUIntLE 4 bytes
  let (channelId, bytes) ← decodeUIntLE 1 bytes
  let (reservedA1, bytes) ← Alpha.decode 1 bytes
  let (marketId, bytes) ← decodeUIntLE 2 bytes
  let (systemId, bytes) ← decodeUIntLE 1 bytes
  let (reservedB1, bytes) ← Alpha.decode 1 bytes
  let (streamId, bytes) ← decodeUIntLE 2 bytes
  let (underlyingIndex, bytes) ← decodeUIntLE 4 bytes
  let (contractMultiplier, bytes) ← decodeUIntLE 2 bytes
  let (maturityDate, bytes) ← Alpha.decode 6 bytes
  let (putOrCall, bytes) ← decodeUIntLE 1 bytes
  let (strikePrice, bytes) ← Alpha.decode 10 bytes
  let (priceScaleCode, bytes) ← decodeUIntLE 1 bytes
  let (underlyingSymbol, bytes) ← Alpha.decode 11 bytes
  let (optionSymbolRoot, bytes) ← Alpha.decode 5 bytes
  let (groupId, bytes) ← decodeUIntLE 4 bytes
  pure ({ seriesIndex, channelId, reservedA1, marketId, systemId, reservedB1, streamId, underlyingIndex, contractMultiplier, maturityDate, putOrCall, strikePrice, priceScaleCode, underlyingSymbol, optionSymbolRoot, groupId }, bytes)

@[simp] theorem encode_length (message : SeriesIndexMappingMessage) : (encode message).length = 56 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : SeriesIndexMappingMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SeriesIndexMappingMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end SeriesIndexMappingMessage

/-- Stream Id Message: 4 bytes -/
structure StreamIdMessage where
  streamId : BitVec 16
  reserved2 : Alpha 2
  deriving DecidableEq, Repr

namespace StreamIdMessage

def encode (message : StreamIdMessage) : List UInt8 :=
  encodeUIntLE 2 message.streamId
    ++ (Alpha.encode message.reserved2)

def decode (bytes : List UInt8) : Option (StreamIdMessage × List UInt8) := do
  let (streamId, bytes) ← decodeUIntLE 2 bytes
  let (reserved2, bytes) ← Alpha.decode 2 bytes
  pure ({ streamId, reserved2 }, bytes)

@[simp] theorem encode_length (message : StreamIdMessage) : (encode message).length = 4 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : StreamIdMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : StreamIdMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end StreamIdMessage

/-- Sequence Number Reset Message: 10 bytes -/
structure SequenceNumberResetMessage where
  sourceTime : BitVec 32
  sourceTimeNs : BitVec 32
  productId : BitVec 8
  channelId : BitVec 8
  deriving DecidableEq, Repr

namespace SequenceNumberResetMessage

def encode (message : SequenceNumberResetMessage) : List UInt8 :=
  encodeUIntLE 4 message.sourceTime
    ++ (encodeUIntLE 4 message.sourceTimeNs
    ++ (encodeUIntLE 1 message.productId
    ++ (encodeUIntLE 1 message.channelId)))

def decode (bytes : List UInt8) : Option (SequenceNumberResetMessage × List UInt8) := do
  let (sourceTime, bytes) ← decodeUIntLE 4 bytes
  let (sourceTimeNs, bytes) ← decodeUIntLE 4 bytes
  let (productId, bytes) ← decodeUIntLE 1 bytes
  let (channelId, bytes) ← decodeUIntLE 1 bytes
  pure ({ sourceTime, sourceTimeNs, productId, channelId }, bytes)

@[simp] theorem encode_length (message : SequenceNumberResetMessage) : (encode message).length = 10 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : SequenceNumberResetMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SequenceNumberResetMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end SequenceNumberResetMessage

/-- Any Payload, selected by Message Type -/
inductive Payload where
  | outrightQuoteMessage (message : OutrightQuoteMessage) -- 401
  | outrightTradeMessage (message : OutrightTradeMessage) -- 407
  | outrightTradeCancelMessage (message : OutrightTradeCancelMessage) -- 409
  | outrightTradeCorrectionMessage (message : OutrightTradeCorrectionMessage) -- 411
  | outrightImbalanceMessage (message : OutrightImbalanceMessage) -- 413
  | outrightCrossingRfqMessage (message : OutrightCrossingRfqMessage) -- 415
  | outrightBoldRfqMessage (message : OutrightBoldRfqMessage) -- 471
  | outrightSummaryMessage (message : OutrightSummaryMessage) -- 417
  | underlyingStatusMessage (message : UnderlyingStatusMessage) -- 419
  | outrightSeriesStatusMessage (message : OutrightSeriesStatusMessage) -- 421
  | refreshOutrightQuoteMessage (message : RefreshOutrightQuoteMessage) -- 501
  | refreshOutrightTradeMessage (message : RefreshOutrightTradeMessage) -- 507
  | refreshOutrightImbalanceMessage (message : RefreshOutrightImbalanceMessage) -- 509
  | underlyingIndexMappingMessage (message : UnderlyingIndexMappingMessage) -- 435
  | seriesIndexMappingMessage (message : SeriesIndexMappingMessage) -- 437
  | streamIdMessage (message : StreamIdMessage) -- 455
  | sequenceNumberResetMessage (message : SequenceNumberResetMessage) -- 1
  deriving DecidableEq, Repr

namespace Payload

/-- The Message Type each message is sent under -/
def tag : Payload → BitVec 16
  | .outrightQuoteMessage _ => 401
  | .outrightTradeMessage _ => 407
  | .outrightTradeCancelMessage _ => 409
  | .outrightTradeCorrectionMessage _ => 411
  | .outrightImbalanceMessage _ => 413
  | .outrightCrossingRfqMessage _ => 415
  | .outrightBoldRfqMessage _ => 471
  | .outrightSummaryMessage _ => 417
  | .underlyingStatusMessage _ => 419
  | .outrightSeriesStatusMessage _ => 421
  | .refreshOutrightQuoteMessage _ => 501
  | .refreshOutrightTradeMessage _ => 507
  | .refreshOutrightImbalanceMessage _ => 509
  | .underlyingIndexMappingMessage _ => 435
  | .seriesIndexMappingMessage _ => 437
  | .streamIdMessage _ => 455
  | .sequenceNumberResetMessage _ => 1

def encode : Payload → List UInt8
  | .outrightQuoteMessage message => OutrightQuoteMessage.encode message
  | .outrightTradeMessage message => OutrightTradeMessage.encode message
  | .outrightTradeCancelMessage message => OutrightTradeCancelMessage.encode message
  | .outrightTradeCorrectionMessage message => OutrightTradeCorrectionMessage.encode message
  | .outrightImbalanceMessage message => OutrightImbalanceMessage.encode message
  | .outrightCrossingRfqMessage message => OutrightCrossingRfqMessage.encode message
  | .outrightBoldRfqMessage message => OutrightBoldRfqMessage.encode message
  | .outrightSummaryMessage message => OutrightSummaryMessage.encode message
  | .underlyingStatusMessage message => UnderlyingStatusMessage.encode message
  | .outrightSeriesStatusMessage message => OutrightSeriesStatusMessage.encode message
  | .refreshOutrightQuoteMessage message => RefreshOutrightQuoteMessage.encode message
  | .refreshOutrightTradeMessage message => RefreshOutrightTradeMessage.encode message
  | .refreshOutrightImbalanceMessage message => RefreshOutrightImbalanceMessage.encode message
  | .underlyingIndexMappingMessage message => UnderlyingIndexMappingMessage.encode message
  | .seriesIndexMappingMessage message => SeriesIndexMappingMessage.encode message
  | .streamIdMessage message => StreamIdMessage.encode message
  | .sequenceNumberResetMessage message => SequenceNumberResetMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : Payload) : (encode message).length ≤ 56 := by
  cases message with
  | outrightQuoteMessage inner =>
    simp only [encode, OutrightQuoteMessage.encode_length]
    omega
  | outrightTradeMessage inner =>
    simp only [encode, OutrightTradeMessage.encode_length]
    omega
  | outrightTradeCancelMessage inner =>
    simp only [encode, OutrightTradeCancelMessage.encode_length]
    omega
  | outrightTradeCorrectionMessage inner =>
    simp only [encode, OutrightTradeCorrectionMessage.encode_length]
    omega
  | outrightImbalanceMessage inner =>
    simp only [encode, OutrightImbalanceMessage.encode_length]
    omega
  | outrightCrossingRfqMessage inner =>
    simp only [encode, OutrightCrossingRfqMessage.encode_length]
    omega
  | outrightBoldRfqMessage inner =>
    simp only [encode, OutrightBoldRfqMessage.encode_length]
    omega
  | outrightSummaryMessage inner =>
    simp only [encode, OutrightSummaryMessage.encode_length]
    omega
  | underlyingStatusMessage inner =>
    simp only [encode, UnderlyingStatusMessage.encode_length]
    omega
  | outrightSeriesStatusMessage inner =>
    simp only [encode, OutrightSeriesStatusMessage.encode_length]
    omega
  | refreshOutrightQuoteMessage inner =>
    simp only [encode, RefreshOutrightQuoteMessage.encode_length]
    omega
  | refreshOutrightTradeMessage inner =>
    simp only [encode, RefreshOutrightTradeMessage.encode_length]
    omega
  | refreshOutrightImbalanceMessage inner =>
    simp only [encode, RefreshOutrightImbalanceMessage.encode_length]
    omega
  | underlyingIndexMappingMessage inner =>
    simp only [encode, UnderlyingIndexMappingMessage.encode_length]
    omega
  | seriesIndexMappingMessage inner =>
    simp only [encode, SeriesIndexMappingMessage.encode_length]
    omega
  | streamIdMessage inner =>
    simp only [encode, StreamIdMessage.encode_length]
    omega
  | sequenceNumberResetMessage inner =>
    simp only [encode, SequenceNumberResetMessage.encode_length]
    omega

def decode (tag : BitVec 16) (bytes : List UInt8) : Option (Payload × List UInt8) :=
  if tag = 401 then (OutrightQuoteMessage.decode bytes).map fun (message, rest) => (.outrightQuoteMessage message, rest)
  else if tag = 407 then (OutrightTradeMessage.decode bytes).map fun (message, rest) => (.outrightTradeMessage message, rest)
  else if tag = 409 then (OutrightTradeCancelMessage.decode bytes).map fun (message, rest) => (.outrightTradeCancelMessage message, rest)
  else if tag = 411 then (OutrightTradeCorrectionMessage.decode bytes).map fun (message, rest) => (.outrightTradeCorrectionMessage message, rest)
  else if tag = 413 then (OutrightImbalanceMessage.decode bytes).map fun (message, rest) => (.outrightImbalanceMessage message, rest)
  else if tag = 415 then (OutrightCrossingRfqMessage.decode bytes).map fun (message, rest) => (.outrightCrossingRfqMessage message, rest)
  else if tag = 471 then (OutrightBoldRfqMessage.decode bytes).map fun (message, rest) => (.outrightBoldRfqMessage message, rest)
  else if tag = 417 then (OutrightSummaryMessage.decode bytes).map fun (message, rest) => (.outrightSummaryMessage message, rest)
  else if tag = 419 then (UnderlyingStatusMessage.decode bytes).map fun (message, rest) => (.underlyingStatusMessage message, rest)
  else if tag = 421 then (OutrightSeriesStatusMessage.decode bytes).map fun (message, rest) => (.outrightSeriesStatusMessage message, rest)
  else if tag = 501 then (RefreshOutrightQuoteMessage.decode bytes).map fun (message, rest) => (.refreshOutrightQuoteMessage message, rest)
  else if tag = 507 then (RefreshOutrightTradeMessage.decode bytes).map fun (message, rest) => (.refreshOutrightTradeMessage message, rest)
  else if tag = 509 then (RefreshOutrightImbalanceMessage.decode bytes).map fun (message, rest) => (.refreshOutrightImbalanceMessage message, rest)
  else if tag = 435 then (UnderlyingIndexMappingMessage.decode bytes).map fun (message, rest) => (.underlyingIndexMappingMessage message, rest)
  else if tag = 437 then (SeriesIndexMappingMessage.decode bytes).map fun (message, rest) => (.seriesIndexMappingMessage message, rest)
  else if tag = 455 then (StreamIdMessage.decode bytes).map fun (message, rest) => (.streamIdMessage message, rest)
  else if tag = 1 then (SequenceNumberResetMessage.decode bytes).map fun (message, rest) => (.sequenceNumberResetMessage message, rest)
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
  encodeUIntLE 2 (Payload.tag message.payload)
    ++ (Payload.encode message.payload)

def decodeBody (bytes : List UInt8) : Option (Message × List UInt8) := do
  let (messageType, bytes) ← decodeUIntLE 2 bytes
  let (payload, bytes) ← Payload.decode messageType bytes
  pure ({ payload }, bytes)

theorem decodeBody_encodeBody (message : Message) (rest : List UInt8) :
    decodeBody (encodeBody message ++ rest) = some (message, rest) := by
  unfold decodeBody encodeBody
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [Payload.decode_encode, some_bind]
  rfl

/-- Every body fits the length prefix -/
theorem encodeBody_length_lt (message : Message) : (encodeBody message).length + 2 < 256 ^ 2 := by
  unfold encodeBody
  cases message.payload with
  | outrightQuoteMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUIntLE_length, OutrightQuoteMessage.encode_length]
    omega
  | outrightTradeMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUIntLE_length, OutrightTradeMessage.encode_length]
    omega
  | outrightTradeCancelMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUIntLE_length, OutrightTradeCancelMessage.encode_length]
    omega
  | outrightTradeCorrectionMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUIntLE_length, OutrightTradeCorrectionMessage.encode_length]
    omega
  | outrightImbalanceMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUIntLE_length, OutrightImbalanceMessage.encode_length]
    omega
  | outrightCrossingRfqMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUIntLE_length, OutrightCrossingRfqMessage.encode_length]
    omega
  | outrightBoldRfqMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUIntLE_length, OutrightBoldRfqMessage.encode_length]
    omega
  | outrightSummaryMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUIntLE_length, OutrightSummaryMessage.encode_length]
    omega
  | underlyingStatusMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUIntLE_length, UnderlyingStatusMessage.encode_length]
    omega
  | outrightSeriesStatusMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUIntLE_length, OutrightSeriesStatusMessage.encode_length]
    omega
  | refreshOutrightQuoteMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUIntLE_length, RefreshOutrightQuoteMessage.encode_length]
    omega
  | refreshOutrightTradeMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUIntLE_length, RefreshOutrightTradeMessage.encode_length]
    omega
  | refreshOutrightImbalanceMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUIntLE_length, RefreshOutrightImbalanceMessage.encode_length]
    omega
  | underlyingIndexMappingMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUIntLE_length, UnderlyingIndexMappingMessage.encode_length]
    omega
  | seriesIndexMappingMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUIntLE_length, SeriesIndexMappingMessage.encode_length]
    omega
  | streamIdMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUIntLE_length, StreamIdMessage.encode_length]
    omega
  | sequenceNumberResetMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUIntLE_length, SequenceNumberResetMessage.encode_length]
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
  packetSize : BitVec 16
  deliveryFlag : BitVec 8
  sequenceNumber : BitVec 32
  sendTime : SendTime
  message : Bounded 1 Message
  deriving DecidableEq, Repr

namespace Packet

def encode (message : Packet) : List UInt8 :=
  encodeUIntLE 2 message.packetSize
    ++ (encodeUIntLE 1 message.deliveryFlag
    ++ (encodeUIntLE 1 (BitVec.ofNat (8 * 1) message.message.val.length)
    ++ (encodeUIntLE 4 message.sequenceNumber
    ++ (SendTime.encode message.sendTime
    ++ (encodeMany Message.encode message.message.val)))))

def decode (bytes : List UInt8) : Option (Packet × List UInt8) := do
  let (packetSize, bytes) ← decodeUIntLE 2 bytes
  let (deliveryFlag, bytes) ← decodeUIntLE 1 bytes
  let (messageCount, bytes) ← decodeUIntLE 1 bytes
  let (sequenceNumber, bytes) ← decodeUIntLE 4 bytes
  let (sendTime, bytes) ← SendTime.decode bytes
  let (message_, bytes) ← decodeMany Message.decode messageCount.toNat bytes
  if fits_message : message_.length < 256 ^ 1 then
    pure ({ packetSize, deliveryFlag, sequenceNumber, sendTime, message := ⟨message_, fits_message⟩ }, bytes)
  else none

theorem encode_length_pos (message : Packet) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

@[simp] theorem decode_encode (message : Packet) (rest : List UInt8) :
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
  rw [List.append_assoc, SendTime.decode_encode, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 Message.encode Message.decode Message.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.message.length_lt]
  rfl

end Packet

end Omi.NyseArcaoptionsTopfeedXdpV13A
