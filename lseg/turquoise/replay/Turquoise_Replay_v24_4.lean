import Wire

/-!
# London Stock Exchange Replay v24.4

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.LsegTurquoiseReplayGtpV244

/-- Login Status: one byte code -/
def LoginStatus.codes : List UInt8 :=
  [0x41, 0x61, 0x62, 0x63, 0x64, 0x65, 0x66]

inductive LoginStatus where
  | loginAccepted -- Login Accepted
  | compIdInactiveSuspended -- Comp Id Inactive Suspended
  | loginLimitReached -- Login Limit Reached
  | serviceUnavailable -- Service Unavailable
  | maximumConnectionsLimitReached -- Maximum Connections Limit Reached
  | failedOther -- Failed Other
  | invalidCompIdOrIpAddress -- Invalid Comp Id Or Ip Address
  | unlisted (byte : { byte : UInt8 // byte ∉ LoginStatus.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace LoginStatus

def toByte : LoginStatus → UInt8
  | .loginAccepted => 0x41
  | .compIdInactiveSuspended => 0x61
  | .loginLimitReached => 0x62
  | .serviceUnavailable => 0x63
  | .maximumConnectionsLimitReached => 0x64
  | .failedOther => 0x65
  | .invalidCompIdOrIpAddress => 0x66
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : LoginStatus :=
  if byte = 0x41 then .loginAccepted
  else if byte = 0x61 then .compIdInactiveSuspended
  else if byte = 0x62 then .loginLimitReached
  else if byte = 0x63 then .serviceUnavailable
  else if byte = 0x64 then .maximumConnectionsLimitReached
  else if byte = 0x65 then .failedOther
  else .invalidCompIdOrIpAddress

def ofByte (byte : UInt8) : LoginStatus :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : LoginStatus) : ofByte value.toByte = value := by
  cases value with
  | loginAccepted => decide
  | compIdInactiveSuspended => decide
  | loginLimitReached => decide
  | serviceUnavailable => decide
  | maximumConnectionsLimitReached => decide
  | failedOther => decide
  | invalidCompIdOrIpAddress => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : LoginStatus) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (LoginStatus × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : LoginStatus) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : LoginStatus) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end LoginStatus

/-- Replay Status: one byte code -/
def ReplayStatus.codes : List UInt8 :=
  [0x41, 0x44, 0x4F, 0x55, 0x63, 0x65]

inductive ReplayStatus where
  | requestAccepted -- Request Accepted
  | requestLimitReached -- Request Limit Reached
  | outOfRange -- Out Of Range
  | replayUnavailable -- Replay Unavailable
  | concurrentLimitReached -- Concurrent Limit Reached
  | failedOther -- Failed Other
  | unlisted (byte : { byte : UInt8 // byte ∉ ReplayStatus.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ReplayStatus

def toByte : ReplayStatus → UInt8
  | .requestAccepted => 0x41
  | .requestLimitReached => 0x44
  | .outOfRange => 0x4F
  | .replayUnavailable => 0x55
  | .concurrentLimitReached => 0x63
  | .failedOther => 0x65
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ReplayStatus :=
  if byte = 0x41 then .requestAccepted
  else if byte = 0x44 then .requestLimitReached
  else if byte = 0x4F then .outOfRange
  else if byte = 0x55 then .replayUnavailable
  else if byte = 0x63 then .concurrentLimitReached
  else .failedOther

def ofByte (byte : UInt8) : ReplayStatus :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ReplayStatus) : ofByte value.toByte = value := by
  cases value with
  | requestAccepted => decide
  | requestLimitReached => decide
  | outOfRange => decide
  | replayUnavailable => decide
  | concurrentLimitReached => decide
  | failedOther => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ReplayStatus) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ReplayStatus × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ReplayStatus) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : ReplayStatus) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ReplayStatus

/-- Trading Status: one byte code -/
def TradingStatus.codes : List UInt8 :=
  [0x48, 0x4A, 0x4B, 0x50, 0x54, 0x74, 0x63, 0x32, 0x77]

inductive TradingStatus where
  | halted -- Halted
  | haltedMatchingPartitionSuspended -- Halted Matching Partition Suspended
  | haltedSystemSuspended -- Halted System Suspended
  | haltedRegulatoryHalt -- Halted Regulatory Halt
  | regularTradingStartOfTrqbSession -- Regular Trading Start Of Trqb Session
  | endOfRegularTradingEndOfTrqbSession -- End Of Regular Trading End Of Trqb Session
  | closed -- Closed
  | suspended -- Suspended
  | noActiveSession -- No Active Session
  | unlisted (byte : { byte : UInt8 // byte ∉ TradingStatus.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TradingStatus

def toByte : TradingStatus → UInt8
  | .halted => 0x48
  | .haltedMatchingPartitionSuspended => 0x4A
  | .haltedSystemSuspended => 0x4B
  | .haltedRegulatoryHalt => 0x50
  | .regularTradingStartOfTrqbSession => 0x54
  | .endOfRegularTradingEndOfTrqbSession => 0x74
  | .closed => 0x63
  | .suspended => 0x32
  | .noActiveSession => 0x77
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TradingStatus :=
  if byte = 0x48 then .halted
  else if byte = 0x4A then .haltedMatchingPartitionSuspended
  else if byte = 0x4B then .haltedSystemSuspended
  else if byte = 0x50 then .haltedRegulatoryHalt
  else if byte = 0x54 then .regularTradingStartOfTrqbSession
  else if byte = 0x74 then .endOfRegularTradingEndOfTrqbSession
  else if byte = 0x63 then .closed
  else if byte = 0x32 then .suspended
  else .noActiveSession

def ofByte (byte : UInt8) : TradingStatus :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TradingStatus) : ofByte value.toByte = value := by
  cases value with
  | halted => decide
  | haltedMatchingPartitionSuspended => decide
  | haltedSystemSuspended => decide
  | haltedRegulatoryHalt => decide
  | regularTradingStartOfTrqbSession => decide
  | endOfRegularTradingEndOfTrqbSession => decide
  | closed => decide
  | suspended => decide
  | noActiveSession => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : TradingStatus) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (TradingStatus × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : TradingStatus) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : TradingStatus) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end TradingStatus

/-- Event Code: one byte code -/
def EventCode.codes : List UInt8 :=
  [0x43, 0x4F]

inductive EventCode where
  | endOfDay -- End Of Day
  | startOfDay -- Start Of Day
  | unlisted (byte : { byte : UInt8 // byte ∉ EventCode.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace EventCode

def toByte : EventCode → UInt8
  | .endOfDay => 0x43
  | .startOfDay => 0x4F
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : EventCode :=
  if byte = 0x43 then .endOfDay
  else .startOfDay

def ofByte (byte : UInt8) : EventCode :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : EventCode) : ofByte value.toByte = value := by
  cases value with
  | endOfDay => decide
  | startOfDay => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : EventCode) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (EventCode × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : EventCode) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : EventCode) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end EventCode

/-- Auction Type: one byte code -/
def AuctionType.codes : List UInt8 :=
  [0x4C]

inductive AuctionType where
  | frequentLitAuctions -- Frequent Lit Auctions
  | unlisted (byte : { byte : UInt8 // byte ∉ AuctionType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace AuctionType

def toByte : AuctionType → UInt8
  | .frequentLitAuctions => 0x4C
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (_ : UInt8) : AuctionType :=
  .frequentLitAuctions

def ofByte (byte : UInt8) : AuctionType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : AuctionType) : ofByte value.toByte = value := by
  cases value with
  | frequentLitAuctions => decide
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

/-- Trade Qualifier: one byte code -/
def TradeQualifier.codes : List UInt8 :=
  [0x20, 0x54]

inductive TradeQualifier where
  | notApplicable -- Not Applicable
  | tradeAtLast -- Trade At Last
  | unlisted (byte : { byte : UInt8 // byte ∉ TradeQualifier.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TradeQualifier

def toByte : TradeQualifier → UInt8
  | .notApplicable => 0x20
  | .tradeAtLast => 0x54
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TradeQualifier :=
  if byte = 0x20 then .notApplicable
  else .tradeAtLast

def ofByte (byte : UInt8) : TradeQualifier :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TradeQualifier) : ofByte value.toByte = value := by
  cases value with
  | notApplicable => decide
  | tradeAtLast => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : TradeQualifier) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (TradeQualifier × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : TradeQualifier) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : TradeQualifier) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end TradeQualifier

/-- Auction Info: one byte code -/
def AuctionInfo.codes : List UInt8 :=
  [0x4D]

inductive AuctionInfo where
  | callMarket -- Call Market
  | unlisted (byte : { byte : UInt8 // byte ∉ AuctionInfo.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace AuctionInfo

def toByte : AuctionInfo → UInt8
  | .callMarket => 0x4D
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (_ : UInt8) : AuctionInfo :=
  .callMarket

def ofByte (byte : UInt8) : AuctionInfo :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : AuctionInfo) : ofByte value.toByte = value := by
  cases value with
  | callMarket => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : AuctionInfo) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (AuctionInfo × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : AuctionInfo) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : AuctionInfo) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end AuctionInfo

/-- Market Mechanism: one byte code -/
def MarketMechanism.codes : List UInt8 :=
  [0x31, 0x33, 0x35]

inductive MarketMechanism where
  | centralLimitOrderBook -- Central Limit Order Book
  | darkOrderBook -- Dark Order Book
  | periodicAuction -- Periodic Auction
  | unlisted (byte : { byte : UInt8 // byte ∉ MarketMechanism.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace MarketMechanism

def toByte : MarketMechanism → UInt8
  | .centralLimitOrderBook => 0x31
  | .darkOrderBook => 0x33
  | .periodicAuction => 0x35
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : MarketMechanism :=
  if byte = 0x31 then .centralLimitOrderBook
  else if byte = 0x33 then .darkOrderBook
  else .periodicAuction

def ofByte (byte : UInt8) : MarketMechanism :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : MarketMechanism) : ofByte value.toByte = value := by
  cases value with
  | centralLimitOrderBook => decide
  | darkOrderBook => decide
  | periodicAuction => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : MarketMechanism) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (MarketMechanism × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : MarketMechanism) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : MarketMechanism) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end MarketMechanism

/-- Trading Mode: one byte code -/
def TradingMode.codes : List UInt8 :=
  [0x55, 0x50, 0x32, 0x33]

inductive TradingMode where
  | unscheduledAuction -- Unscheduled Auction
  | onDemandAuction -- On Demand Auction
  | continuousTrading -- Continuous Trading
  | atMarketCloseTrading -- At Market Close Trading
  | unlisted (byte : { byte : UInt8 // byte ∉ TradingMode.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TradingMode

def toByte : TradingMode → UInt8
  | .unscheduledAuction => 0x55
  | .onDemandAuction => 0x50
  | .continuousTrading => 0x32
  | .atMarketCloseTrading => 0x33
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TradingMode :=
  if byte = 0x55 then .unscheduledAuction
  else if byte = 0x50 then .onDemandAuction
  else if byte = 0x32 then .continuousTrading
  else .atMarketCloseTrading

def ofByte (byte : UInt8) : TradingMode :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TradingMode) : ofByte value.toByte = value := by
  cases value with
  | unscheduledAuction => decide
  | onDemandAuction => decide
  | continuousTrading => decide
  | atMarketCloseTrading => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : TradingMode) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (TradingMode × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : TradingMode) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : TradingMode) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end TradingMode

/-- Transaction Category: one byte code -/
def TransactionCategory.codes : List UInt8 :=
  [0x44, 0x2D]

inductive TransactionCategory where
  | darkTrade -- Dark Trade
  | none_ -- None
  | unlisted (byte : { byte : UInt8 // byte ∉ TransactionCategory.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TransactionCategory

def toByte : TransactionCategory → UInt8
  | .darkTrade => 0x44
  | .none_ => 0x2D
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TransactionCategory :=
  if byte = 0x44 then .darkTrade
  else .none_

def ofByte (byte : UInt8) : TransactionCategory :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TransactionCategory) : ofByte value.toByte = value := by
  cases value with
  | darkTrade => decide
  | none_ => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : TransactionCategory) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (TransactionCategory × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : TransactionCategory) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : TransactionCategory) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end TransactionCategory

/-- Negotiation Indicator: one byte code -/
def NegotiationIndicator.codes : List UInt8 :=
  [0x38, 0x2D]

inductive NegotiationIndicator where
  | negotiatedTradeWithPretradeTransparencyWaiver -- Negotiated Trade With Pretrade Transparency Waiver
  | notANegotiatedTrade -- Not A Negotiated Trade
  | unlisted (byte : { byte : UInt8 // byte ∉ NegotiationIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace NegotiationIndicator

def toByte : NegotiationIndicator → UInt8
  | .negotiatedTradeWithPretradeTransparencyWaiver => 0x38
  | .notANegotiatedTrade => 0x2D
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : NegotiationIndicator :=
  if byte = 0x38 then .negotiatedTradeWithPretradeTransparencyWaiver
  else .notANegotiatedTrade

def ofByte (byte : UInt8) : NegotiationIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : NegotiationIndicator) : ofByte value.toByte = value := by
  cases value with
  | negotiatedTradeWithPretradeTransparencyWaiver => decide
  | notANegotiatedTrade => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : NegotiationIndicator) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (NegotiationIndicator × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : NegotiationIndicator) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : NegotiationIndicator) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end NegotiationIndicator

/-- Agency Cross Indicator: one byte code -/
def AgencyCrossIndicator.codes : List UInt8 :=
  [0x2D]

inductive AgencyCrossIndicator where
  | noAgencyCrossTrade -- No Agency Cross Trade
  | unlisted (byte : { byte : UInt8 // byte ∉ AgencyCrossIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace AgencyCrossIndicator

def toByte : AgencyCrossIndicator → UInt8
  | .noAgencyCrossTrade => 0x2D
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (_ : UInt8) : AgencyCrossIndicator :=
  .noAgencyCrossTrade

def ofByte (byte : UInt8) : AgencyCrossIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : AgencyCrossIndicator) : ofByte value.toByte = value := by
  cases value with
  | noAgencyCrossTrade => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : AgencyCrossIndicator) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (AgencyCrossIndicator × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : AgencyCrossIndicator) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : AgencyCrossIndicator) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end AgencyCrossIndicator

/-- Modification Indicator: one byte code -/
def ModificationIndicator.codes : List UInt8 :=
  [0x43, 0x41, 0x2D]

inductive ModificationIndicator where
  | tradeCancellation -- Trade Cancellation
  | tradeAmendment -- Trade Amendment
  | newTrade -- New Trade
  | unlisted (byte : { byte : UInt8 // byte ∉ ModificationIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ModificationIndicator

def toByte : ModificationIndicator → UInt8
  | .tradeCancellation => 0x43
  | .tradeAmendment => 0x41
  | .newTrade => 0x2D
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ModificationIndicator :=
  if byte = 0x43 then .tradeCancellation
  else if byte = 0x41 then .tradeAmendment
  else .newTrade

def ofByte (byte : UInt8) : ModificationIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ModificationIndicator) : ofByte value.toByte = value := by
  cases value with
  | tradeCancellation => decide
  | tradeAmendment => decide
  | newTrade => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ModificationIndicator) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ModificationIndicator × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ModificationIndicator) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : ModificationIndicator) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ModificationIndicator

/-- Reference Price Indicator: one byte code -/
def ReferencePriceIndicator.codes : List UInt8 :=
  [0x53, 0x31, 0x2D]

inductive ReferencePriceIndicator where
  | referencePriceTrade -- Reference Price Trade
  | marketClosingPriceTrade -- Market Closing Price Trade
  | notAReferencePriceTrade -- Not A Reference Price Trade
  | unlisted (byte : { byte : UInt8 // byte ∉ ReferencePriceIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ReferencePriceIndicator

def toByte : ReferencePriceIndicator → UInt8
  | .referencePriceTrade => 0x53
  | .marketClosingPriceTrade => 0x31
  | .notAReferencePriceTrade => 0x2D
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ReferencePriceIndicator :=
  if byte = 0x53 then .referencePriceTrade
  else if byte = 0x31 then .marketClosingPriceTrade
  else .notAReferencePriceTrade

def ofByte (byte : UInt8) : ReferencePriceIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ReferencePriceIndicator) : ofByte value.toByte = value := by
  cases value with
  | referencePriceTrade => decide
  | marketClosingPriceTrade => decide
  | notAReferencePriceTrade => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ReferencePriceIndicator) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ReferencePriceIndicator × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ReferencePriceIndicator) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : ReferencePriceIndicator) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ReferencePriceIndicator

/-- Special Dividend Indicator: one byte code -/
def SpecialDividendIndicator.codes : List UInt8 :=
  [0x2D]

inductive SpecialDividendIndicator where
  | noSpecialDividendTrade -- No Special Dividend Trade
  | unlisted (byte : { byte : UInt8 // byte ∉ SpecialDividendIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace SpecialDividendIndicator

def toByte : SpecialDividendIndicator → UInt8
  | .noSpecialDividendTrade => 0x2D
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (_ : UInt8) : SpecialDividendIndicator :=
  .noSpecialDividendTrade

def ofByte (byte : UInt8) : SpecialDividendIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : SpecialDividendIndicator) : ofByte value.toByte = value := by
  cases value with
  | noSpecialDividendTrade => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : SpecialDividendIndicator) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (SpecialDividendIndicator × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : SpecialDividendIndicator) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : SpecialDividendIndicator) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end SpecialDividendIndicator

/-- Off Book Automated Indicator: one byte code -/
def OffBookAutomatedIndicator.codes : List UInt8 :=
  [0x2D]

inductive OffBookAutomatedIndicator where
  | unspecifiedOrDoesNotApply -- Unspecified Or Does Not Apply
  | unlisted (byte : { byte : UInt8 // byte ∉ OffBookAutomatedIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OffBookAutomatedIndicator

def toByte : OffBookAutomatedIndicator → UInt8
  | .unspecifiedOrDoesNotApply => 0x2D
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (_ : UInt8) : OffBookAutomatedIndicator :=
  .unspecifiedOrDoesNotApply

def ofByte (byte : UInt8) : OffBookAutomatedIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OffBookAutomatedIndicator) : ofByte value.toByte = value := by
  cases value with
  | unspecifiedOrDoesNotApply => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : OffBookAutomatedIndicator) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (OffBookAutomatedIndicator × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : OffBookAutomatedIndicator) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : OffBookAutomatedIndicator) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end OffBookAutomatedIndicator

/-- Price Formation Indicator: one byte code -/
def PriceFormationIndicator.codes : List UInt8 :=
  [0x50]

inductive PriceFormationIndicator where
  | plainVanillaTrade -- Plain Vanilla Trade
  | unlisted (byte : { byte : UInt8 // byte ∉ PriceFormationIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace PriceFormationIndicator

def toByte : PriceFormationIndicator → UInt8
  | .plainVanillaTrade => 0x50
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (_ : UInt8) : PriceFormationIndicator :=
  .plainVanillaTrade

def ofByte (byte : UInt8) : PriceFormationIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : PriceFormationIndicator) : ofByte value.toByte = value := by
  cases value with
  | plainVanillaTrade => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : PriceFormationIndicator) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (PriceFormationIndicator × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : PriceFormationIndicator) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : PriceFormationIndicator) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end PriceFormationIndicator

/-- Algorithmic Indicator: one byte code -/
def AlgorithmicIndicator.codes : List UInt8 :=
  [0x48, 0x2D]

inductive AlgorithmicIndicator where
  | algorithmicTrade -- Algorithmic Trade
  | notAnAlgorithmicTrade -- Not An Algorithmic Trade
  | unlisted (byte : { byte : UInt8 // byte ∉ AlgorithmicIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace AlgorithmicIndicator

def toByte : AlgorithmicIndicator → UInt8
  | .algorithmicTrade => 0x48
  | .notAnAlgorithmicTrade => 0x2D
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : AlgorithmicIndicator :=
  if byte = 0x48 then .algorithmicTrade
  else .notAnAlgorithmicTrade

def ofByte (byte : UInt8) : AlgorithmicIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : AlgorithmicIndicator) : ofByte value.toByte = value := by
  cases value with
  | algorithmicTrade => decide
  | notAnAlgorithmicTrade => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : AlgorithmicIndicator) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (AlgorithmicIndicator × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : AlgorithmicIndicator) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : AlgorithmicIndicator) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end AlgorithmicIndicator

/-- Post Trade Deferral Reason: one byte code -/
def PostTradeDeferralReason.codes : List UInt8 :=
  [0x2D]

inductive PostTradeDeferralReason where
  | immediatePublication -- Immediate Publication
  | unlisted (byte : { byte : UInt8 // byte ∉ PostTradeDeferralReason.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace PostTradeDeferralReason

def toByte : PostTradeDeferralReason → UInt8
  | .immediatePublication => 0x2D
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (_ : UInt8) : PostTradeDeferralReason :=
  .immediatePublication

def ofByte (byte : UInt8) : PostTradeDeferralReason :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : PostTradeDeferralReason) : ofByte value.toByte = value := by
  cases value with
  | immediatePublication => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : PostTradeDeferralReason) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (PostTradeDeferralReason × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : PostTradeDeferralReason) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : PostTradeDeferralReason) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end PostTradeDeferralReason

/-- Duplicative Indicator: one byte code -/
def DuplicativeIndicator.codes : List UInt8 :=
  [0x2D]

inductive DuplicativeIndicator where
  | uniqueTradeReport -- Unique Trade Report
  | unlisted (byte : { byte : UInt8 // byte ∉ DuplicativeIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace DuplicativeIndicator

def toByte : DuplicativeIndicator → UInt8
  | .uniqueTradeReport => 0x2D
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (_ : UInt8) : DuplicativeIndicator :=
  .uniqueTradeReport

def ofByte (byte : UInt8) : DuplicativeIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : DuplicativeIndicator) : ofByte value.toByte = value := by
  cases value with
  | uniqueTradeReport => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : DuplicativeIndicator) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (DuplicativeIndicator × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : DuplicativeIndicator) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : DuplicativeIndicator) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end DuplicativeIndicator

/-- Login Request Message: 8 bytes -/
structure LoginRequestMessage where
  username : Alpha 8
  deriving DecidableEq, Repr

namespace LoginRequestMessage

def encode (message : LoginRequestMessage) : List UInt8 :=
  Alpha.encode message.username

def decode (bytes : List UInt8) : Option (LoginRequestMessage × List UInt8) := do
  let (username, bytes) ← Alpha.decode 8 bytes
  pure ({ username }, bytes)

@[simp] theorem encode_length (message : LoginRequestMessage) : (encode message).length = 8 := by
  unfold encode
  simp only [Alpha.encode_length]

theorem encode_length_pos (message : LoginRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LoginRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [Alpha.decode_encode, some_bind]
  rfl

end LoginRequestMessage

/-- Replay Request Message: 12 bytes -/
structure ReplayRequestMessage where
  firstMessage : BitVec 32
  count : BitVec 32
  requestId : BitVec 32
  deriving DecidableEq, Repr

namespace ReplayRequestMessage

def encode (message : ReplayRequestMessage) : List UInt8 :=
  encodeUIntLE 4 message.firstMessage
    ++ (encodeUIntLE 4 message.count
    ++ (encodeUIntLE 4 message.requestId))

def decode (bytes : List UInt8) : Option (ReplayRequestMessage × List UInt8) := do
  let (firstMessage, bytes) ← decodeUIntLE 4 bytes
  let (count, bytes) ← decodeUIntLE 4 bytes
  let (requestId, bytes) ← decodeUIntLE 4 bytes
  pure ({ firstMessage, count, requestId }, bytes)

@[simp] theorem encode_length (message : ReplayRequestMessage) : (encode message).length = 12 := by
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
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end ReplayRequestMessage

/-- Login Response Message: 1 bytes -/
structure LoginResponseMessage where
  loginStatus : LoginStatus
  deriving DecidableEq, Repr

namespace LoginResponseMessage

def encode (message : LoginResponseMessage) : List UInt8 :=
  LoginStatus.encode message.loginStatus

def decode (bytes : List UInt8) : Option (LoginResponseMessage × List UInt8) := do
  let (loginStatus, bytes) ← LoginStatus.decode bytes
  pure ({ loginStatus }, bytes)

@[simp] theorem encode_length (message : LoginResponseMessage) : (encode message).length = 1 := by
  unfold encode
  simp only [LoginStatus.encode_length]

theorem encode_length_pos (message : LoginResponseMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LoginResponseMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [LoginStatus.decode_encode, some_bind]
  rfl

end LoginResponseMessage

/-- Replay Response Message: 13 bytes -/
structure ReplayResponseMessage where
  firstMessage : BitVec 32
  count : BitVec 32
  replayStatus : ReplayStatus
  requestId : BitVec 32
  deriving DecidableEq, Repr

namespace ReplayResponseMessage

def encode (message : ReplayResponseMessage) : List UInt8 :=
  encodeUIntLE 4 message.firstMessage
    ++ (encodeUIntLE 4 message.count
    ++ (ReplayStatus.encode message.replayStatus
    ++ (encodeUIntLE 4 message.requestId)))

def decode (bytes : List UInt8) : Option (ReplayResponseMessage × List UInt8) := do
  let (firstMessage, bytes) ← decodeUIntLE 4 bytes
  let (count, bytes) ← decodeUIntLE 4 bytes
  let (replayStatus, bytes) ← ReplayStatus.decode bytes
  let (requestId, bytes) ← decodeUIntLE 4 bytes
  pure ({ firstMessage, count, replayStatus, requestId }, bytes)

@[simp] theorem encode_length (message : ReplayResponseMessage) : (encode message).length = 13 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, ReplayStatus.encode_length]

theorem encode_length_pos (message : ReplayResponseMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ReplayResponseMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, ReplayStatus.decode_encode, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end ReplayResponseMessage

/-- Replay And Recovery Complete Message: 5 bytes -/
structure ReplayAndRecoveryCompleteMessage where
  requestId : BitVec 32
  tradingStatus : TradingStatus
  deriving DecidableEq, Repr

namespace ReplayAndRecoveryCompleteMessage

def encode (message : ReplayAndRecoveryCompleteMessage) : List UInt8 :=
  encodeUIntLE 4 message.requestId
    ++ (TradingStatus.encode message.tradingStatus)

def decode (bytes : List UInt8) : Option (ReplayAndRecoveryCompleteMessage × List UInt8) := do
  let (requestId, bytes) ← decodeUIntLE 4 bytes
  let (tradingStatus, bytes) ← TradingStatus.decode bytes
  pure ({ requestId, tradingStatus }, bytes)

@[simp] theorem encode_length (message : ReplayAndRecoveryCompleteMessage) : (encode message).length = 5 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, TradingStatus.encode_length]

theorem encode_length_pos (message : ReplayAndRecoveryCompleteMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ReplayAndRecoveryCompleteMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [TradingStatus.decode_encode, some_bind]
  rfl

end ReplayAndRecoveryCompleteMessage

/-- System Event Message: 11 bytes -/
structure SystemEventMessage where
  timestamp : BitVec 64
  eventCode : EventCode
  sourceVenue : BitVec 16
  deriving DecidableEq, Repr

namespace SystemEventMessage

def encode (message : SystemEventMessage) : List UInt8 :=
  encodeUIntLE 8 message.timestamp
    ++ (EventCode.encode message.eventCode
    ++ (encodeUIntLE 2 message.sourceVenue))

def decode (bytes : List UInt8) : Option (SystemEventMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  let (eventCode, bytes) ← EventCode.decode bytes
  let (sourceVenue, bytes) ← decodeUIntLE 2 bytes
  pure ({ timestamp, eventCode, sourceVenue }, bytes)

@[simp] theorem encode_length (message : SystemEventMessage) : (encode message).length = 11 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, EventCode.encode_length]

theorem encode_length_pos (message : SystemEventMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SystemEventMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, EventCode.decode_encode, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end SystemEventMessage

/-- Instrument Directory Message: 138 bytes -/
structure InstrumentDirectoryMessage where
  timestamp : BitVec 64
  instrument : BitVec 64
  isin : Alpha 12
  allowedBookTypes : BitVec 8
  sourceVenue : BitVec 16
  venueInstrumentId : Alpha 11
  tickId : Alpha 2
  priceBandTolerances : BitVec 64
  dynamicCircuitBreakerTolerances : BitVec 64
  staticCircuitBreakerTolerances : BitVec 64
  segment : Alpha 6
  reserved12 : Alpha 12
  reserved11 : Alpha 11
  currency : Alpha 3
  reserved1 : Alpha 1
  reserved4 : Alpha 4
  averageDailyTurnoverAdt : BitVec 64
  reserved8 : Alpha 8
  secondReserved1 : Alpha 1
  secondReserved8 : Alpha 8
  thirdReserved8 : Alpha 8
  deriving DecidableEq, Repr

namespace InstrumentDirectoryMessage

def encode (message : InstrumentDirectoryMessage) : List UInt8 :=
  encodeUIntLE 8 message.timestamp
    ++ (encodeUIntLE 8 message.instrument
    ++ (Alpha.encode message.isin
    ++ (encodeUIntLE 1 message.allowedBookTypes
    ++ (encodeUIntLE 2 message.sourceVenue
    ++ (Alpha.encode message.venueInstrumentId
    ++ (Alpha.encode message.tickId
    ++ (encodeUIntLE 8 message.priceBandTolerances
    ++ (encodeUIntLE 8 message.dynamicCircuitBreakerTolerances
    ++ (encodeUIntLE 8 message.staticCircuitBreakerTolerances
    ++ (Alpha.encode message.segment
    ++ (Alpha.encode message.reserved12
    ++ (Alpha.encode message.reserved11
    ++ (Alpha.encode message.currency
    ++ (Alpha.encode message.reserved1
    ++ (Alpha.encode message.reserved4
    ++ (encodeUIntLE 8 message.averageDailyTurnoverAdt
    ++ (Alpha.encode message.reserved8
    ++ (Alpha.encode message.secondReserved1
    ++ (Alpha.encode message.secondReserved8
    ++ (Alpha.encode message.thirdReserved8))))))))))))))))))))

def decode (bytes : List UInt8) : Option (InstrumentDirectoryMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  let (instrument, bytes) ← decodeUIntLE 8 bytes
  let (isin, bytes) ← Alpha.decode 12 bytes
  let (allowedBookTypes, bytes) ← decodeUIntLE 1 bytes
  let (sourceVenue, bytes) ← decodeUIntLE 2 bytes
  let (venueInstrumentId, bytes) ← Alpha.decode 11 bytes
  let (tickId, bytes) ← Alpha.decode 2 bytes
  let (priceBandTolerances, bytes) ← decodeUIntLE 8 bytes
  let (dynamicCircuitBreakerTolerances, bytes) ← decodeUIntLE 8 bytes
  let (staticCircuitBreakerTolerances, bytes) ← decodeUIntLE 8 bytes
  let (segment, bytes) ← Alpha.decode 6 bytes
  let (reserved12, bytes) ← Alpha.decode 12 bytes
  let (reserved11, bytes) ← Alpha.decode 11 bytes
  let (currency, bytes) ← Alpha.decode 3 bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  let (reserved4, bytes) ← Alpha.decode 4 bytes
  let (averageDailyTurnoverAdt, bytes) ← decodeUIntLE 8 bytes
  let (reserved8, bytes) ← Alpha.decode 8 bytes
  let (secondReserved1, bytes) ← Alpha.decode 1 bytes
  let (secondReserved8, bytes) ← Alpha.decode 8 bytes
  let (thirdReserved8, bytes) ← Alpha.decode 8 bytes
  pure ({ timestamp, instrument, isin, allowedBookTypes, sourceVenue, venueInstrumentId, tickId, priceBandTolerances, dynamicCircuitBreakerTolerances, staticCircuitBreakerTolerances, segment, reserved12, reserved11, currency, reserved1, reserved4, averageDailyTurnoverAdt, reserved8, secondReserved1, secondReserved8, thirdReserved8 }, bytes)

@[simp] theorem encode_length (message : InstrumentDirectoryMessage) : (encode message).length = 138 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : InstrumentDirectoryMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : InstrumentDirectoryMessage) (rest : List UInt8) :
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
  rw [Alpha.decode_encode, some_bind]
  rfl

end InstrumentDirectoryMessage

/-- Instrument Status Message: 27 bytes -/
structure InstrumentStatusMessage where
  timestamp : BitVec 64
  instrument : BitVec 64
  sourceVenue : BitVec 16
  tradingStatus : TradingStatus
  sessionChangeReason : BitVec 8
  newEndTime : Alpha 6
  orderBookType : BitVec 8
  deriving DecidableEq, Repr

namespace InstrumentStatusMessage

def encode (message : InstrumentStatusMessage) : List UInt8 :=
  encodeUIntLE 8 message.timestamp
    ++ (encodeUIntLE 8 message.instrument
    ++ (encodeUIntLE 2 message.sourceVenue
    ++ (TradingStatus.encode message.tradingStatus
    ++ (encodeUIntLE 1 message.sessionChangeReason
    ++ (Alpha.encode message.newEndTime
    ++ (encodeUIntLE 1 message.orderBookType))))))

def decode (bytes : List UInt8) : Option (InstrumentStatusMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  let (instrument, bytes) ← decodeUIntLE 8 bytes
  let (sourceVenue, bytes) ← decodeUIntLE 2 bytes
  let (tradingStatus, bytes) ← TradingStatus.decode bytes
  let (sessionChangeReason, bytes) ← decodeUIntLE 1 bytes
  let (newEndTime, bytes) ← Alpha.decode 6 bytes
  let (orderBookType, bytes) ← decodeUIntLE 1 bytes
  pure ({ timestamp, instrument, sourceVenue, tradingStatus, sessionChangeReason, newEndTime, orderBookType }, bytes)

@[simp] theorem encode_length (message : InstrumentStatusMessage) : (encode message).length = 27 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, TradingStatus.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : InstrumentStatusMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : InstrumentStatusMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, TradingStatus.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end InstrumentStatusMessage

/-- Add Order Incremental Message: 74 bytes -/
structure AddOrderIncrementalMessage where
  timestamp : BitVec 64
  orderId : BitVec 64
  side : Alpha 1
  size : BitVec 64
  instrument : BitVec 64
  price : BitVec 64
  transactionTime : BitVec 64
  sourceVenue : BitVec 16
  orderBookType : BitVec 8
  participant : Alpha 11
  orderType : BitVec 8
  rfqId : Alpha 10
  deriving DecidableEq, Repr

namespace AddOrderIncrementalMessage

def encode (message : AddOrderIncrementalMessage) : List UInt8 :=
  encodeUIntLE 8 message.timestamp
    ++ (encodeUIntLE 8 message.orderId
    ++ (Alpha.encode message.side
    ++ (encodeUIntLE 8 message.size
    ++ (encodeUIntLE 8 message.instrument
    ++ (encodeUIntLE 8 message.price
    ++ (encodeUIntLE 8 message.transactionTime
    ++ (encodeUIntLE 2 message.sourceVenue
    ++ (encodeUIntLE 1 message.orderBookType
    ++ (Alpha.encode message.participant
    ++ (encodeUIntLE 1 message.orderType
    ++ (Alpha.encode message.rfqId)))))))))))

def decode (bytes : List UInt8) : Option (AddOrderIncrementalMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (side, bytes) ← Alpha.decode 1 bytes
  let (size, bytes) ← decodeUIntLE 8 bytes
  let (instrument, bytes) ← decodeUIntLE 8 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (transactionTime, bytes) ← decodeUIntLE 8 bytes
  let (sourceVenue, bytes) ← decodeUIntLE 2 bytes
  let (orderBookType, bytes) ← decodeUIntLE 1 bytes
  let (participant, bytes) ← Alpha.decode 11 bytes
  let (orderType, bytes) ← decodeUIntLE 1 bytes
  let (rfqId, bytes) ← Alpha.decode 10 bytes
  pure ({ timestamp, orderId, side, size, instrument, price, transactionTime, sourceVenue, orderBookType, participant, orderType, rfqId }, bytes)

@[simp] theorem encode_length (message : AddOrderIncrementalMessage) : (encode message).length = 74 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : AddOrderIncrementalMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : AddOrderIncrementalMessage) (rest : List UInt8) :
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
  rw [Alpha.decode_encode, some_bind]
  rfl

end AddOrderIncrementalMessage

/-- Order Modify Message: 77 bytes -/
structure OrderModifyMessage where
  timestamp : BitVec 64
  orderId : BitVec 64
  instrument : BitVec 64
  side : Alpha 1
  orderModifyFlags : BitVec 8
  orderBookType : BitVec 8
  newQuantity : BitVec 64
  newPrice : BitVec 64
  reserved8 : Alpha 8
  sourceVenue : BitVec 16
  previousPrice : BitVec 64
  previousQuantity : BitVec 64
  transactionTime : BitVec 64
  deriving DecidableEq, Repr

namespace OrderModifyMessage

def encode (message : OrderModifyMessage) : List UInt8 :=
  encodeUIntLE 8 message.timestamp
    ++ (encodeUIntLE 8 message.orderId
    ++ (encodeUIntLE 8 message.instrument
    ++ (Alpha.encode message.side
    ++ (encodeUIntLE 1 message.orderModifyFlags
    ++ (encodeUIntLE 1 message.orderBookType
    ++ (encodeUIntLE 8 message.newQuantity
    ++ (encodeUIntLE 8 message.newPrice
    ++ (Alpha.encode message.reserved8
    ++ (encodeUIntLE 2 message.sourceVenue
    ++ (encodeUIntLE 8 message.previousPrice
    ++ (encodeUIntLE 8 message.previousQuantity
    ++ (encodeUIntLE 8 message.transactionTime))))))))))))

def decode (bytes : List UInt8) : Option (OrderModifyMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (instrument, bytes) ← decodeUIntLE 8 bytes
  let (side, bytes) ← Alpha.decode 1 bytes
  let (orderModifyFlags, bytes) ← decodeUIntLE 1 bytes
  let (orderBookType, bytes) ← decodeUIntLE 1 bytes
  let (newQuantity, bytes) ← decodeUIntLE 8 bytes
  let (newPrice, bytes) ← decodeUIntLE 8 bytes
  let (reserved8, bytes) ← Alpha.decode 8 bytes
  let (sourceVenue, bytes) ← decodeUIntLE 2 bytes
  let (previousPrice, bytes) ← decodeUIntLE 8 bytes
  let (previousQuantity, bytes) ← decodeUIntLE 8 bytes
  let (transactionTime, bytes) ← decodeUIntLE 8 bytes
  pure ({ timestamp, orderId, instrument, side, orderModifyFlags, orderBookType, newQuantity, newPrice, reserved8, sourceVenue, previousPrice, previousQuantity, transactionTime }, bytes)

@[simp] theorem encode_length (message : OrderModifyMessage) : (encode message).length = 77 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : OrderModifyMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderModifyMessage) (rest : List UInt8) :
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
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end OrderModifyMessage

/-- Order Delete Message: 52 bytes -/
structure OrderDeleteMessage where
  timestamp : BitVec 64
  orderId : BitVec 64
  instrument : BitVec 64
  side : Alpha 1
  orderBookType : BitVec 8
  sourceVenue : BitVec 16
  previousPrice : BitVec 64
  previousQuantity : BitVec 64
  transactionTime : BitVec 64
  deriving DecidableEq, Repr

namespace OrderDeleteMessage

def encode (message : OrderDeleteMessage) : List UInt8 :=
  encodeUIntLE 8 message.timestamp
    ++ (encodeUIntLE 8 message.orderId
    ++ (encodeUIntLE 8 message.instrument
    ++ (Alpha.encode message.side
    ++ (encodeUIntLE 1 message.orderBookType
    ++ (encodeUIntLE 2 message.sourceVenue
    ++ (encodeUIntLE 8 message.previousPrice
    ++ (encodeUIntLE 8 message.previousQuantity
    ++ (encodeUIntLE 8 message.transactionTime))))))))

def decode (bytes : List UInt8) : Option (OrderDeleteMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (instrument, bytes) ← decodeUIntLE 8 bytes
  let (side, bytes) ← Alpha.decode 1 bytes
  let (orderBookType, bytes) ← decodeUIntLE 1 bytes
  let (sourceVenue, bytes) ← decodeUIntLE 2 bytes
  let (previousPrice, bytes) ← decodeUIntLE 8 bytes
  let (previousQuantity, bytes) ← decodeUIntLE 8 bytes
  let (transactionTime, bytes) ← decodeUIntLE 8 bytes
  pure ({ timestamp, orderId, instrument, side, orderBookType, sourceVenue, previousPrice, previousQuantity, transactionTime }, bytes)

@[simp] theorem encode_length (message : OrderDeleteMessage) : (encode message).length = 52 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : OrderDeleteMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderDeleteMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end OrderDeleteMessage

/-- Top Of Book Message: 84 bytes -/
structure TopOfBookMessage where
  timestamp : BitVec 64
  instrument : BitVec 64
  sourceVenue : BitVec 16
  bidMarketSize : BitVec 64
  bidLimitPrice : BitVec 64
  reserved8 : Alpha 8
  bidLimitSize : BitVec 64
  offerMarketSize : BitVec 64
  offerLimitPrice : BitVec 64
  secondReserved8 : Alpha 8
  offerLimitSize : BitVec 64
  orderBookType : BitVec 8
  topOfBookFlags : BitVec 8
  deriving DecidableEq, Repr

namespace TopOfBookMessage

def encode (message : TopOfBookMessage) : List UInt8 :=
  encodeUIntLE 8 message.timestamp
    ++ (encodeUIntLE 8 message.instrument
    ++ (encodeUIntLE 2 message.sourceVenue
    ++ (encodeUIntLE 8 message.bidMarketSize
    ++ (encodeUIntLE 8 message.bidLimitPrice
    ++ (Alpha.encode message.reserved8
    ++ (encodeUIntLE 8 message.bidLimitSize
    ++ (encodeUIntLE 8 message.offerMarketSize
    ++ (encodeUIntLE 8 message.offerLimitPrice
    ++ (Alpha.encode message.secondReserved8
    ++ (encodeUIntLE 8 message.offerLimitSize
    ++ (encodeUIntLE 1 message.orderBookType
    ++ (encodeUIntLE 1 message.topOfBookFlags))))))))))))

def decode (bytes : List UInt8) : Option (TopOfBookMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  let (instrument, bytes) ← decodeUIntLE 8 bytes
  let (sourceVenue, bytes) ← decodeUIntLE 2 bytes
  let (bidMarketSize, bytes) ← decodeUIntLE 8 bytes
  let (bidLimitPrice, bytes) ← decodeUIntLE 8 bytes
  let (reserved8, bytes) ← Alpha.decode 8 bytes
  let (bidLimitSize, bytes) ← decodeUIntLE 8 bytes
  let (offerMarketSize, bytes) ← decodeUIntLE 8 bytes
  let (offerLimitPrice, bytes) ← decodeUIntLE 8 bytes
  let (secondReserved8, bytes) ← Alpha.decode 8 bytes
  let (offerLimitSize, bytes) ← decodeUIntLE 8 bytes
  let (orderBookType, bytes) ← decodeUIntLE 1 bytes
  let (topOfBookFlags, bytes) ← decodeUIntLE 1 bytes
  pure ({ timestamp, instrument, sourceVenue, bidMarketSize, bidLimitPrice, reserved8, bidLimitSize, offerMarketSize, offerLimitPrice, secondReserved8, offerLimitSize, orderBookType, topOfBookFlags }, bytes)

@[simp] theorem encode_length (message : TopOfBookMessage) : (encode message).length = 84 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : TopOfBookMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TopOfBookMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end TopOfBookMessage

/-- Order Book Clear Message: 19 bytes -/
structure OrderBookClearMessage where
  timestamp : BitVec 64
  sourceVenue : BitVec 16
  instrument : BitVec 64
  orderBookType : BitVec 8
  deriving DecidableEq, Repr

namespace OrderBookClearMessage

def encode (message : OrderBookClearMessage) : List UInt8 :=
  encodeUIntLE 8 message.timestamp
    ++ (encodeUIntLE 2 message.sourceVenue
    ++ (encodeUIntLE 8 message.instrument
    ++ (encodeUIntLE 1 message.orderBookType)))

def decode (bytes : List UInt8) : Option (OrderBookClearMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  let (sourceVenue, bytes) ← decodeUIntLE 2 bytes
  let (instrument, bytes) ← decodeUIntLE 8 bytes
  let (orderBookType, bytes) ← decodeUIntLE 1 bytes
  pure ({ timestamp, sourceVenue, instrument, orderBookType }, bytes)

@[simp] theorem encode_length (message : OrderBookClearMessage) : (encode message).length = 19 := by
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
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end OrderBookClearMessage

/-- Trade Message: 63 bytes -/
structure TradeMessage where
  timestamp : BitVec 64
  transactionTime : BitVec 64
  sourceVenue : BitVec 16
  executedSize : BitVec 64
  instrument : BitVec 64
  price : BitVec 64
  reserved8 : Alpha 8
  tradeId : BitVec 64
  tradeType : BitVec 8
  auctionType : AuctionType
  tradeFlags : BitVec 8
  hiddenExecutionIndicator : BitVec 8
  tradeQualifier : TradeQualifier
  deriving DecidableEq, Repr

namespace TradeMessage

def encode (message : TradeMessage) : List UInt8 :=
  encodeUIntLE 8 message.timestamp
    ++ (encodeUIntLE 8 message.transactionTime
    ++ (encodeUIntLE 2 message.sourceVenue
    ++ (encodeUIntLE 8 message.executedSize
    ++ (encodeUIntLE 8 message.instrument
    ++ (encodeUIntLE 8 message.price
    ++ (Alpha.encode message.reserved8
    ++ (encodeUIntLE 8 message.tradeId
    ++ (encodeUIntLE 1 message.tradeType
    ++ (AuctionType.encode message.auctionType
    ++ (encodeUIntLE 1 message.tradeFlags
    ++ (encodeUIntLE 1 message.hiddenExecutionIndicator
    ++ (TradeQualifier.encode message.tradeQualifier))))))))))))

def decode (bytes : List UInt8) : Option (TradeMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  let (transactionTime, bytes) ← decodeUIntLE 8 bytes
  let (sourceVenue, bytes) ← decodeUIntLE 2 bytes
  let (executedSize, bytes) ← decodeUIntLE 8 bytes
  let (instrument, bytes) ← decodeUIntLE 8 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (reserved8, bytes) ← Alpha.decode 8 bytes
  let (tradeId, bytes) ← decodeUIntLE 8 bytes
  let (tradeType, bytes) ← decodeUIntLE 1 bytes
  let (auctionType, bytes) ← AuctionType.decode bytes
  let (tradeFlags, bytes) ← decodeUIntLE 1 bytes
  let (hiddenExecutionIndicator, bytes) ← decodeUIntLE 1 bytes
  let (tradeQualifier, bytes) ← TradeQualifier.decode bytes
  pure ({ timestamp, transactionTime, sourceVenue, executedSize, instrument, price, reserved8, tradeId, tradeType, auctionType, tradeFlags, hiddenExecutionIndicator, tradeQualifier }, bytes)

@[simp] theorem encode_length (message : TradeMessage) : (encode message).length = 63 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, AuctionType.encode_length, TradeQualifier.encode_length]

theorem encode_length_pos (message : TradeMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradeMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, AuctionType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [TradeQualifier.decode_encode, some_bind]
  rfl

end TradeMessage

/-- Trade Cross Message: 80 bytes -/
structure TradeCrossMessage where
  timestamp : BitVec 64
  transactionTime : BitVec 64
  sourceVenue : BitVec 16
  executedSize : BitVec 64
  instrument : BitVec 64
  price : BitVec 64
  reserved8 : Alpha 8
  tradeId : BitVec 64
  crossId : Alpha 20
  crossType : BitVec 8
  tradeFlags : BitVec 8
  deriving DecidableEq, Repr

namespace TradeCrossMessage

def encode (message : TradeCrossMessage) : List UInt8 :=
  encodeUIntLE 8 message.timestamp
    ++ (encodeUIntLE 8 message.transactionTime
    ++ (encodeUIntLE 2 message.sourceVenue
    ++ (encodeUIntLE 8 message.executedSize
    ++ (encodeUIntLE 8 message.instrument
    ++ (encodeUIntLE 8 message.price
    ++ (Alpha.encode message.reserved8
    ++ (encodeUIntLE 8 message.tradeId
    ++ (Alpha.encode message.crossId
    ++ (encodeUIntLE 1 message.crossType
    ++ (encodeUIntLE 1 message.tradeFlags))))))))))

def decode (bytes : List UInt8) : Option (TradeCrossMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  let (transactionTime, bytes) ← decodeUIntLE 8 bytes
  let (sourceVenue, bytes) ← decodeUIntLE 2 bytes
  let (executedSize, bytes) ← decodeUIntLE 8 bytes
  let (instrument, bytes) ← decodeUIntLE 8 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (reserved8, bytes) ← Alpha.decode 8 bytes
  let (tradeId, bytes) ← decodeUIntLE 8 bytes
  let (crossId, bytes) ← Alpha.decode 20 bytes
  let (crossType, bytes) ← decodeUIntLE 1 bytes
  let (tradeFlags, bytes) ← decodeUIntLE 1 bytes
  pure ({ timestamp, transactionTime, sourceVenue, executedSize, instrument, price, reserved8, tradeId, crossId, crossType, tradeFlags }, bytes)

@[simp] theorem encode_length (message : TradeCrossMessage) : (encode message).length = 80 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : TradeCrossMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradeCrossMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end TradeCrossMessage

/-- Statistics Message: 74 bytes -/
structure StatisticsMessage where
  timestamp : BitVec 64
  instrument : BitVec 64
  sourceVenue : BitVec 16
  volume : BitVec 64
  volumeOnbookOnly : BitVec 64
  vwap : BitVec 64
  vwapOnbookOnly : BitVec 64
  numberOfTrades : BitVec 32
  numberOfTradesOnbookOnly : BitVec 32
  turnover : BitVec 64
  turnoverOnbookOnly : BitVec 64
  deriving DecidableEq, Repr

namespace StatisticsMessage

def encode (message : StatisticsMessage) : List UInt8 :=
  encodeUIntLE 8 message.timestamp
    ++ (encodeUIntLE 8 message.instrument
    ++ (encodeUIntLE 2 message.sourceVenue
    ++ (encodeUIntLE 8 message.volume
    ++ (encodeUIntLE 8 message.volumeOnbookOnly
    ++ (encodeUIntLE 8 message.vwap
    ++ (encodeUIntLE 8 message.vwapOnbookOnly
    ++ (encodeUIntLE 4 message.numberOfTrades
    ++ (encodeUIntLE 4 message.numberOfTradesOnbookOnly
    ++ (encodeUIntLE 8 message.turnover
    ++ (encodeUIntLE 8 message.turnoverOnbookOnly))))))))))

def decode (bytes : List UInt8) : Option (StatisticsMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  let (instrument, bytes) ← decodeUIntLE 8 bytes
  let (sourceVenue, bytes) ← decodeUIntLE 2 bytes
  let (volume, bytes) ← decodeUIntLE 8 bytes
  let (volumeOnbookOnly, bytes) ← decodeUIntLE 8 bytes
  let (vwap, bytes) ← decodeUIntLE 8 bytes
  let (vwapOnbookOnly, bytes) ← decodeUIntLE 8 bytes
  let (numberOfTrades, bytes) ← decodeUIntLE 4 bytes
  let (numberOfTradesOnbookOnly, bytes) ← decodeUIntLE 4 bytes
  let (turnover, bytes) ← decodeUIntLE 8 bytes
  let (turnoverOnbookOnly, bytes) ← decodeUIntLE 8 bytes
  pure ({ timestamp, instrument, sourceVenue, volume, volumeOnbookOnly, vwap, vwapOnbookOnly, numberOfTrades, numberOfTradesOnbookOnly, turnover, turnoverOnbookOnly }, bytes)

@[simp] theorem encode_length (message : StatisticsMessage) : (encode message).length = 74 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

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

end StatisticsMessage

/-- Statistics Update Message: 47 bytes -/
structure StatisticsUpdateMessage where
  timestamp : BitVec 64
  instrument : BitVec 64
  sourceVenue : BitVec 16
  statisticType : BitVec 16
  statisticPrice : BitVec 64
  statisticSize : BitVec 64
  auctionType : AuctionType
  imbalanceQuantity : BitVec 64
  auctionInfo : AuctionInfo
  openingClosingPriceIndicator : Alpha 1
  deriving DecidableEq, Repr

namespace StatisticsUpdateMessage

def encode (message : StatisticsUpdateMessage) : List UInt8 :=
  encodeUIntLE 8 message.timestamp
    ++ (encodeUIntLE 8 message.instrument
    ++ (encodeUIntLE 2 message.sourceVenue
    ++ (encodeUIntLE 2 message.statisticType
    ++ (encodeUIntLE 8 message.statisticPrice
    ++ (encodeUIntLE 8 message.statisticSize
    ++ (AuctionType.encode message.auctionType
    ++ (encodeUIntLE 8 message.imbalanceQuantity
    ++ (AuctionInfo.encode message.auctionInfo
    ++ (Alpha.encode message.openingClosingPriceIndicator)))))))))

def decode (bytes : List UInt8) : Option (StatisticsUpdateMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  let (instrument, bytes) ← decodeUIntLE 8 bytes
  let (sourceVenue, bytes) ← decodeUIntLE 2 bytes
  let (statisticType, bytes) ← decodeUIntLE 2 bytes
  let (statisticPrice, bytes) ← decodeUIntLE 8 bytes
  let (statisticSize, bytes) ← decodeUIntLE 8 bytes
  let (auctionType, bytes) ← AuctionType.decode bytes
  let (imbalanceQuantity, bytes) ← decodeUIntLE 8 bytes
  let (auctionInfo, bytes) ← AuctionInfo.decode bytes
  let (openingClosingPriceIndicator, bytes) ← Alpha.decode 1 bytes
  pure ({ timestamp, instrument, sourceVenue, statisticType, statisticPrice, statisticSize, auctionType, imbalanceQuantity, auctionInfo, openingClosingPriceIndicator }, bytes)

@[simp] theorem encode_length (message : StatisticsUpdateMessage) : (encode message).length = 47 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, AuctionType.encode_length, AuctionInfo.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : StatisticsUpdateMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : StatisticsUpdateMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, AuctionType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, AuctionInfo.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end StatisticsUpdateMessage

/-- Mifid Ii Trade Message: 283 bytes -/
structure MifidIiTradeMessage where
  timestamp : BitVec 64
  sourceVenue : BitVec 16
  instrument : BitVec 64
  transactionIdentificationCode : Alpha 52
  tradeType : BitVec 8
  auctionType : AuctionType
  miFidPrice : Alpha 20
  miFidQuantity : Alpha 20
  tradingDateAndTime : Alpha 27
  instrumentIdentificationCodeType : Alpha 4
  instrumentIdentificationCode : Alpha 12
  priceNotation : Alpha 4
  priceMajorCurrency : Alpha 3
  notionalAmount : Alpha 20
  notionalCurrency : Alpha 3
  venueOfExecution : Alpha 4
  publicationDateAndTime : Alpha 27
  ptRefPriceWaiverFlag : Alpha 4
  reserved4 : Alpha 4
  marketClosingPriceFlag : Alpha 4
  ptAlgoTrade : Alpha 4
  ptCancellationFlag : Alpha 4
  ptAmendmentFlag : Alpha 4
  reserved1 : Alpha 1
  reserved3 : Alpha 3
  reserved20 : Alpha 20
  secondReserved4 : Alpha 4
  tradeQualifier : TradeQualifier
  marketMechanism : MarketMechanism
  tradingMode : TradingMode
  transactionCategory : TransactionCategory
  negotiationIndicator : NegotiationIndicator
  agencyCrossIndicator : AgencyCrossIndicator
  modificationIndicator : ModificationIndicator
  referencePriceIndicator : ReferencePriceIndicator
  specialDividendIndicator : SpecialDividendIndicator
  offBookAutomatedIndicator : OffBookAutomatedIndicator
  priceFormationIndicator : PriceFormationIndicator
  algorithmicIndicator : AlgorithmicIndicator
  postTradeDeferralReason : PostTradeDeferralReason
  deferralEnrichmentType : Alpha 1
  duplicativeIndicator : DuplicativeIndicator
  deriving DecidableEq, Repr

namespace MifidIiTradeMessage

def encode (message : MifidIiTradeMessage) : List UInt8 :=
  encodeUIntLE 8 message.timestamp
    ++ (encodeUIntLE 2 message.sourceVenue
    ++ (encodeUIntLE 8 message.instrument
    ++ (Alpha.encode message.transactionIdentificationCode
    ++ (encodeUIntLE 1 message.tradeType
    ++ (AuctionType.encode message.auctionType
    ++ (Alpha.encode message.miFidPrice
    ++ (Alpha.encode message.miFidQuantity
    ++ (Alpha.encode message.tradingDateAndTime
    ++ (Alpha.encode message.instrumentIdentificationCodeType
    ++ (Alpha.encode message.instrumentIdentificationCode
    ++ (Alpha.encode message.priceNotation
    ++ (Alpha.encode message.priceMajorCurrency
    ++ (Alpha.encode message.notionalAmount
    ++ (Alpha.encode message.notionalCurrency
    ++ (Alpha.encode message.venueOfExecution
    ++ (Alpha.encode message.publicationDateAndTime
    ++ (Alpha.encode message.ptRefPriceWaiverFlag
    ++ (Alpha.encode message.reserved4
    ++ (Alpha.encode message.marketClosingPriceFlag
    ++ (Alpha.encode message.ptAlgoTrade
    ++ (Alpha.encode message.ptCancellationFlag
    ++ (Alpha.encode message.ptAmendmentFlag
    ++ (Alpha.encode message.reserved1
    ++ (Alpha.encode message.reserved3
    ++ (Alpha.encode message.reserved20
    ++ (Alpha.encode message.secondReserved4
    ++ (TradeQualifier.encode message.tradeQualifier
    ++ (MarketMechanism.encode message.marketMechanism
    ++ (TradingMode.encode message.tradingMode
    ++ (TransactionCategory.encode message.transactionCategory
    ++ (NegotiationIndicator.encode message.negotiationIndicator
    ++ (AgencyCrossIndicator.encode message.agencyCrossIndicator
    ++ (ModificationIndicator.encode message.modificationIndicator
    ++ (ReferencePriceIndicator.encode message.referencePriceIndicator
    ++ (SpecialDividendIndicator.encode message.specialDividendIndicator
    ++ (OffBookAutomatedIndicator.encode message.offBookAutomatedIndicator
    ++ (PriceFormationIndicator.encode message.priceFormationIndicator
    ++ (AlgorithmicIndicator.encode message.algorithmicIndicator
    ++ (PostTradeDeferralReason.encode message.postTradeDeferralReason
    ++ (Alpha.encode message.deferralEnrichmentType
    ++ (DuplicativeIndicator.encode message.duplicativeIndicator)))))))))))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (MifidIiTradeMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  let (sourceVenue, bytes) ← decodeUIntLE 2 bytes
  let (instrument, bytes) ← decodeUIntLE 8 bytes
  let (transactionIdentificationCode, bytes) ← Alpha.decode 52 bytes
  let (tradeType, bytes) ← decodeUIntLE 1 bytes
  let (auctionType, bytes) ← AuctionType.decode bytes
  let (miFidPrice, bytes) ← Alpha.decode 20 bytes
  let (miFidQuantity, bytes) ← Alpha.decode 20 bytes
  let (tradingDateAndTime, bytes) ← Alpha.decode 27 bytes
  let (instrumentIdentificationCodeType, bytes) ← Alpha.decode 4 bytes
  let (instrumentIdentificationCode, bytes) ← Alpha.decode 12 bytes
  let (priceNotation, bytes) ← Alpha.decode 4 bytes
  let (priceMajorCurrency, bytes) ← Alpha.decode 3 bytes
  let (notionalAmount, bytes) ← Alpha.decode 20 bytes
  let (notionalCurrency, bytes) ← Alpha.decode 3 bytes
  let (venueOfExecution, bytes) ← Alpha.decode 4 bytes
  let (publicationDateAndTime, bytes) ← Alpha.decode 27 bytes
  let (ptRefPriceWaiverFlag, bytes) ← Alpha.decode 4 bytes
  let (reserved4, bytes) ← Alpha.decode 4 bytes
  let (marketClosingPriceFlag, bytes) ← Alpha.decode 4 bytes
  let (ptAlgoTrade, bytes) ← Alpha.decode 4 bytes
  let (ptCancellationFlag, bytes) ← Alpha.decode 4 bytes
  let (ptAmendmentFlag, bytes) ← Alpha.decode 4 bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  let (reserved3, bytes) ← Alpha.decode 3 bytes
  let (reserved20, bytes) ← Alpha.decode 20 bytes
  let (secondReserved4, bytes) ← Alpha.decode 4 bytes
  let (tradeQualifier, bytes) ← TradeQualifier.decode bytes
  let (marketMechanism, bytes) ← MarketMechanism.decode bytes
  let (tradingMode, bytes) ← TradingMode.decode bytes
  let (transactionCategory, bytes) ← TransactionCategory.decode bytes
  let (negotiationIndicator, bytes) ← NegotiationIndicator.decode bytes
  let (agencyCrossIndicator, bytes) ← AgencyCrossIndicator.decode bytes
  let (modificationIndicator, bytes) ← ModificationIndicator.decode bytes
  let (referencePriceIndicator, bytes) ← ReferencePriceIndicator.decode bytes
  let (specialDividendIndicator, bytes) ← SpecialDividendIndicator.decode bytes
  let (offBookAutomatedIndicator, bytes) ← OffBookAutomatedIndicator.decode bytes
  let (priceFormationIndicator, bytes) ← PriceFormationIndicator.decode bytes
  let (algorithmicIndicator, bytes) ← AlgorithmicIndicator.decode bytes
  let (postTradeDeferralReason, bytes) ← PostTradeDeferralReason.decode bytes
  let (deferralEnrichmentType, bytes) ← Alpha.decode 1 bytes
  let (duplicativeIndicator, bytes) ← DuplicativeIndicator.decode bytes
  pure ({ timestamp, sourceVenue, instrument, transactionIdentificationCode, tradeType, auctionType, miFidPrice, miFidQuantity, tradingDateAndTime, instrumentIdentificationCodeType, instrumentIdentificationCode, priceNotation, priceMajorCurrency, notionalAmount, notionalCurrency, venueOfExecution, publicationDateAndTime, ptRefPriceWaiverFlag, reserved4, marketClosingPriceFlag, ptAlgoTrade, ptCancellationFlag, ptAmendmentFlag, reserved1, reserved3, reserved20, secondReserved4, tradeQualifier, marketMechanism, tradingMode, transactionCategory, negotiationIndicator, agencyCrossIndicator, modificationIndicator, referencePriceIndicator, specialDividendIndicator, offBookAutomatedIndicator, priceFormationIndicator, algorithmicIndicator, postTradeDeferralReason, deferralEnrichmentType, duplicativeIndicator }, bytes)

@[simp] theorem encode_length (message : MifidIiTradeMessage) : (encode message).length = 283 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, AuctionType.encode_length, TradeQualifier.encode_length, MarketMechanism.encode_length, TradingMode.encode_length, TransactionCategory.encode_length, NegotiationIndicator.encode_length, AgencyCrossIndicator.encode_length, ModificationIndicator.encode_length, ReferencePriceIndicator.encode_length, SpecialDividendIndicator.encode_length, OffBookAutomatedIndicator.encode_length, PriceFormationIndicator.encode_length, AlgorithmicIndicator.encode_length, PostTradeDeferralReason.encode_length, DuplicativeIndicator.encode_length]

theorem encode_length_pos (message : MifidIiTradeMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : MifidIiTradeMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, AuctionType.decode_encode, some_bind]
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
  rw [List.append_assoc, TradeQualifier.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, MarketMechanism.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TradingMode.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TransactionCategory.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, NegotiationIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, AgencyCrossIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ModificationIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ReferencePriceIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SpecialDividendIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OffBookAutomatedIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, PriceFormationIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, AlgorithmicIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, PostTradeDeferralReason.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [DuplicativeIndicator.decode_encode, some_bind]
  rfl

end MifidIiTradeMessage

/-- Mi Fid Ii Trade Cross Message: 301 bytes -/
structure MiFidIiTradeCrossMessage where
  timestamp : BitVec 64
  sourceVenue : BitVec 16
  instrument : BitVec 64
  transactionIdentificationCode : Alpha 52
  crossId : Alpha 20
  crossType : BitVec 8
  miFidPrice : Alpha 20
  miFidQuantity : Alpha 20
  tradingDateAndTime : Alpha 27
  instrumentIdentificationCodeType : Alpha 4
  instrumentIdentificationCode : Alpha 12
  priceNotation : Alpha 4
  priceMajorCurrency : Alpha 3
  notionalAmount : Alpha 20
  notionalCurrency : Alpha 3
  venueOfExecution : Alpha 4
  publicationDateAndTime : Alpha 27
  reserved4 : Alpha 4
  ntPreTradeWaiverFlag : Alpha 4
  ptAlgoTrade : Alpha 4
  secondReserved4 : Alpha 4
  ptCancellationFlag : Alpha 4
  ptAmendmentFlag : Alpha 4
  reserved1 : Alpha 1
  reserved3 : Alpha 3
  reserved20 : Alpha 20
  thirdReserved4 : Alpha 4
  marketMechanism : MarketMechanism
  tradingMode : TradingMode
  transactionCategory : TransactionCategory
  negotiationIndicator : NegotiationIndicator
  agencyCrossIndicator : AgencyCrossIndicator
  modificationIndicator : ModificationIndicator
  referencePriceIndicator : ReferencePriceIndicator
  specialDividendIndicator : SpecialDividendIndicator
  offBookAutomatedIndicator : OffBookAutomatedIndicator
  priceFormationIndicator : PriceFormationIndicator
  algorithmicIndicator : AlgorithmicIndicator
  postTradeDeferralReason : PostTradeDeferralReason
  deferralEnrichmentType : Alpha 1
  duplicativeIndicator : DuplicativeIndicator
  deriving DecidableEq, Repr

namespace MiFidIiTradeCrossMessage

def encode (message : MiFidIiTradeCrossMessage) : List UInt8 :=
  encodeUIntLE 8 message.timestamp
    ++ (encodeUIntLE 2 message.sourceVenue
    ++ (encodeUIntLE 8 message.instrument
    ++ (Alpha.encode message.transactionIdentificationCode
    ++ (Alpha.encode message.crossId
    ++ (encodeUIntLE 1 message.crossType
    ++ (Alpha.encode message.miFidPrice
    ++ (Alpha.encode message.miFidQuantity
    ++ (Alpha.encode message.tradingDateAndTime
    ++ (Alpha.encode message.instrumentIdentificationCodeType
    ++ (Alpha.encode message.instrumentIdentificationCode
    ++ (Alpha.encode message.priceNotation
    ++ (Alpha.encode message.priceMajorCurrency
    ++ (Alpha.encode message.notionalAmount
    ++ (Alpha.encode message.notionalCurrency
    ++ (Alpha.encode message.venueOfExecution
    ++ (Alpha.encode message.publicationDateAndTime
    ++ (Alpha.encode message.reserved4
    ++ (Alpha.encode message.ntPreTradeWaiverFlag
    ++ (Alpha.encode message.ptAlgoTrade
    ++ (Alpha.encode message.secondReserved4
    ++ (Alpha.encode message.ptCancellationFlag
    ++ (Alpha.encode message.ptAmendmentFlag
    ++ (Alpha.encode message.reserved1
    ++ (Alpha.encode message.reserved3
    ++ (Alpha.encode message.reserved20
    ++ (Alpha.encode message.thirdReserved4
    ++ (MarketMechanism.encode message.marketMechanism
    ++ (TradingMode.encode message.tradingMode
    ++ (TransactionCategory.encode message.transactionCategory
    ++ (NegotiationIndicator.encode message.negotiationIndicator
    ++ (AgencyCrossIndicator.encode message.agencyCrossIndicator
    ++ (ModificationIndicator.encode message.modificationIndicator
    ++ (ReferencePriceIndicator.encode message.referencePriceIndicator
    ++ (SpecialDividendIndicator.encode message.specialDividendIndicator
    ++ (OffBookAutomatedIndicator.encode message.offBookAutomatedIndicator
    ++ (PriceFormationIndicator.encode message.priceFormationIndicator
    ++ (AlgorithmicIndicator.encode message.algorithmicIndicator
    ++ (PostTradeDeferralReason.encode message.postTradeDeferralReason
    ++ (Alpha.encode message.deferralEnrichmentType
    ++ (DuplicativeIndicator.encode message.duplicativeIndicator))))))))))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (MiFidIiTradeCrossMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  let (sourceVenue, bytes) ← decodeUIntLE 2 bytes
  let (instrument, bytes) ← decodeUIntLE 8 bytes
  let (transactionIdentificationCode, bytes) ← Alpha.decode 52 bytes
  let (crossId, bytes) ← Alpha.decode 20 bytes
  let (crossType, bytes) ← decodeUIntLE 1 bytes
  let (miFidPrice, bytes) ← Alpha.decode 20 bytes
  let (miFidQuantity, bytes) ← Alpha.decode 20 bytes
  let (tradingDateAndTime, bytes) ← Alpha.decode 27 bytes
  let (instrumentIdentificationCodeType, bytes) ← Alpha.decode 4 bytes
  let (instrumentIdentificationCode, bytes) ← Alpha.decode 12 bytes
  let (priceNotation, bytes) ← Alpha.decode 4 bytes
  let (priceMajorCurrency, bytes) ← Alpha.decode 3 bytes
  let (notionalAmount, bytes) ← Alpha.decode 20 bytes
  let (notionalCurrency, bytes) ← Alpha.decode 3 bytes
  let (venueOfExecution, bytes) ← Alpha.decode 4 bytes
  let (publicationDateAndTime, bytes) ← Alpha.decode 27 bytes
  let (reserved4, bytes) ← Alpha.decode 4 bytes
  let (ntPreTradeWaiverFlag, bytes) ← Alpha.decode 4 bytes
  let (ptAlgoTrade, bytes) ← Alpha.decode 4 bytes
  let (secondReserved4, bytes) ← Alpha.decode 4 bytes
  let (ptCancellationFlag, bytes) ← Alpha.decode 4 bytes
  let (ptAmendmentFlag, bytes) ← Alpha.decode 4 bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  let (reserved3, bytes) ← Alpha.decode 3 bytes
  let (reserved20, bytes) ← Alpha.decode 20 bytes
  let (thirdReserved4, bytes) ← Alpha.decode 4 bytes
  let (marketMechanism, bytes) ← MarketMechanism.decode bytes
  let (tradingMode, bytes) ← TradingMode.decode bytes
  let (transactionCategory, bytes) ← TransactionCategory.decode bytes
  let (negotiationIndicator, bytes) ← NegotiationIndicator.decode bytes
  let (agencyCrossIndicator, bytes) ← AgencyCrossIndicator.decode bytes
  let (modificationIndicator, bytes) ← ModificationIndicator.decode bytes
  let (referencePriceIndicator, bytes) ← ReferencePriceIndicator.decode bytes
  let (specialDividendIndicator, bytes) ← SpecialDividendIndicator.decode bytes
  let (offBookAutomatedIndicator, bytes) ← OffBookAutomatedIndicator.decode bytes
  let (priceFormationIndicator, bytes) ← PriceFormationIndicator.decode bytes
  let (algorithmicIndicator, bytes) ← AlgorithmicIndicator.decode bytes
  let (postTradeDeferralReason, bytes) ← PostTradeDeferralReason.decode bytes
  let (deferralEnrichmentType, bytes) ← Alpha.decode 1 bytes
  let (duplicativeIndicator, bytes) ← DuplicativeIndicator.decode bytes
  pure ({ timestamp, sourceVenue, instrument, transactionIdentificationCode, crossId, crossType, miFidPrice, miFidQuantity, tradingDateAndTime, instrumentIdentificationCodeType, instrumentIdentificationCode, priceNotation, priceMajorCurrency, notionalAmount, notionalCurrency, venueOfExecution, publicationDateAndTime, reserved4, ntPreTradeWaiverFlag, ptAlgoTrade, secondReserved4, ptCancellationFlag, ptAmendmentFlag, reserved1, reserved3, reserved20, thirdReserved4, marketMechanism, tradingMode, transactionCategory, negotiationIndicator, agencyCrossIndicator, modificationIndicator, referencePriceIndicator, specialDividendIndicator, offBookAutomatedIndicator, priceFormationIndicator, algorithmicIndicator, postTradeDeferralReason, deferralEnrichmentType, duplicativeIndicator }, bytes)

@[simp] theorem encode_length (message : MiFidIiTradeCrossMessage) : (encode message).length = 301 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, MarketMechanism.encode_length, TradingMode.encode_length, TransactionCategory.encode_length, NegotiationIndicator.encode_length, AgencyCrossIndicator.encode_length, ModificationIndicator.encode_length, ReferencePriceIndicator.encode_length, SpecialDividendIndicator.encode_length, OffBookAutomatedIndicator.encode_length, PriceFormationIndicator.encode_length, AlgorithmicIndicator.encode_length, PostTradeDeferralReason.encode_length, DuplicativeIndicator.encode_length]

theorem encode_length_pos (message : MiFidIiTradeCrossMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : MiFidIiTradeCrossMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, MarketMechanism.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TradingMode.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TransactionCategory.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, NegotiationIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, AgencyCrossIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ModificationIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ReferencePriceIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SpecialDividendIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OffBookAutomatedIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, PriceFormationIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, AlgorithmicIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, PostTradeDeferralReason.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [DuplicativeIndicator.decode_encode, some_bind]
  rfl

end MiFidIiTradeCrossMessage

/-- Trade Summary Message: 91 bytes -/
structure TradeSummaryMessage where
  timestamp : BitVec 64
  instrument : BitVec 64
  sourceVenue : BitVec 16
  transactionTime : BitVec 64
  farPrice : BitVec 64
  totalExecutedQuantity : BitVec 64
  totalHiddenExecutedQuantity : BitVec 64
  deletedOrderQuantity : BitVec 64
  side : Alpha 1
  bestBidSize : BitVec 64
  bestBidPrice : BitVec 64
  bestOfferSize : BitVec 64
  bestOfferPrice : BitVec 64
  deriving DecidableEq, Repr

namespace TradeSummaryMessage

def encode (message : TradeSummaryMessage) : List UInt8 :=
  encodeUIntLE 8 message.timestamp
    ++ (encodeUIntLE 8 message.instrument
    ++ (encodeUIntLE 2 message.sourceVenue
    ++ (encodeUIntLE 8 message.transactionTime
    ++ (encodeUIntLE 8 message.farPrice
    ++ (encodeUIntLE 8 message.totalExecutedQuantity
    ++ (encodeUIntLE 8 message.totalHiddenExecutedQuantity
    ++ (encodeUIntLE 8 message.deletedOrderQuantity
    ++ (Alpha.encode message.side
    ++ (encodeUIntLE 8 message.bestBidSize
    ++ (encodeUIntLE 8 message.bestBidPrice
    ++ (encodeUIntLE 8 message.bestOfferSize
    ++ (encodeUIntLE 8 message.bestOfferPrice))))))))))))

def decode (bytes : List UInt8) : Option (TradeSummaryMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  let (instrument, bytes) ← decodeUIntLE 8 bytes
  let (sourceVenue, bytes) ← decodeUIntLE 2 bytes
  let (transactionTime, bytes) ← decodeUIntLE 8 bytes
  let (farPrice, bytes) ← decodeUIntLE 8 bytes
  let (totalExecutedQuantity, bytes) ← decodeUIntLE 8 bytes
  let (totalHiddenExecutedQuantity, bytes) ← decodeUIntLE 8 bytes
  let (deletedOrderQuantity, bytes) ← decodeUIntLE 8 bytes
  let (side, bytes) ← Alpha.decode 1 bytes
  let (bestBidSize, bytes) ← decodeUIntLE 8 bytes
  let (bestBidPrice, bytes) ← decodeUIntLE 8 bytes
  let (bestOfferSize, bytes) ← decodeUIntLE 8 bytes
  let (bestOfferPrice, bytes) ← decodeUIntLE 8 bytes
  pure ({ timestamp, instrument, sourceVenue, transactionTime, farPrice, totalExecutedQuantity, totalHiddenExecutedQuantity, deletedOrderQuantity, side, bestBidSize, bestBidPrice, bestOfferSize, bestOfferPrice }, bytes)

@[simp] theorem encode_length (message : TradeSummaryMessage) : (encode message).length = 91 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : TradeSummaryMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradeSummaryMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end TradeSummaryMessage

/-- Analytics Message: 106 bytes -/
structure AnalyticsMessage where
  timestamp : BitVec 64
  instrument : BitVec 64
  sourceVenue : BitVec 16
  startTime : BitVec 64
  endTime : BitVec 64
  buyOrderCount : BitVec 32
  sellOrderCount : BitVec 32
  buyOrderSize : BitVec 64
  sellOrderSize : BitVec 64
  buyOrderCancellations : BitVec 32
  sellOrderCancellations : BitVec 32
  buyLimitOrderCancellations : BitVec 32
  buyMarketOrderCancellations : BitVec 32
  sellLimitOrderCancellations : BitVec 32
  sellMarketOrderCancellations : BitVec 32
  bidAskSpread : BitVec 64
  vwapBuy : BitVec 64
  vwapSell : BitVec 64
  deriving DecidableEq, Repr

namespace AnalyticsMessage

def encode (message : AnalyticsMessage) : List UInt8 :=
  encodeUIntLE 8 message.timestamp
    ++ (encodeUIntLE 8 message.instrument
    ++ (encodeUIntLE 2 message.sourceVenue
    ++ (encodeUIntLE 8 message.startTime
    ++ (encodeUIntLE 8 message.endTime
    ++ (encodeUIntLE 4 message.buyOrderCount
    ++ (encodeUIntLE 4 message.sellOrderCount
    ++ (encodeUIntLE 8 message.buyOrderSize
    ++ (encodeUIntLE 8 message.sellOrderSize
    ++ (encodeUIntLE 4 message.buyOrderCancellations
    ++ (encodeUIntLE 4 message.sellOrderCancellations
    ++ (encodeUIntLE 4 message.buyLimitOrderCancellations
    ++ (encodeUIntLE 4 message.buyMarketOrderCancellations
    ++ (encodeUIntLE 4 message.sellLimitOrderCancellations
    ++ (encodeUIntLE 4 message.sellMarketOrderCancellations
    ++ (encodeUIntLE 8 message.bidAskSpread
    ++ (encodeUIntLE 8 message.vwapBuy
    ++ (encodeUIntLE 8 message.vwapSell)))))))))))))))))

def decode (bytes : List UInt8) : Option (AnalyticsMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  let (instrument, bytes) ← decodeUIntLE 8 bytes
  let (sourceVenue, bytes) ← decodeUIntLE 2 bytes
  let (startTime, bytes) ← decodeUIntLE 8 bytes
  let (endTime, bytes) ← decodeUIntLE 8 bytes
  let (buyOrderCount, bytes) ← decodeUIntLE 4 bytes
  let (sellOrderCount, bytes) ← decodeUIntLE 4 bytes
  let (buyOrderSize, bytes) ← decodeUIntLE 8 bytes
  let (sellOrderSize, bytes) ← decodeUIntLE 8 bytes
  let (buyOrderCancellations, bytes) ← decodeUIntLE 4 bytes
  let (sellOrderCancellations, bytes) ← decodeUIntLE 4 bytes
  let (buyLimitOrderCancellations, bytes) ← decodeUIntLE 4 bytes
  let (buyMarketOrderCancellations, bytes) ← decodeUIntLE 4 bytes
  let (sellLimitOrderCancellations, bytes) ← decodeUIntLE 4 bytes
  let (sellMarketOrderCancellations, bytes) ← decodeUIntLE 4 bytes
  let (bidAskSpread, bytes) ← decodeUIntLE 8 bytes
  let (vwapBuy, bytes) ← decodeUIntLE 8 bytes
  let (vwapSell, bytes) ← decodeUIntLE 8 bytes
  pure ({ timestamp, instrument, sourceVenue, startTime, endTime, buyOrderCount, sellOrderCount, buyOrderSize, sellOrderSize, buyOrderCancellations, sellOrderCancellations, buyLimitOrderCancellations, buyMarketOrderCancellations, sellLimitOrderCancellations, sellMarketOrderCancellations, bidAskSpread, vwapBuy, vwapSell }, bytes)

@[simp] theorem encode_length (message : AnalyticsMessage) : (encode message).length = 106 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : AnalyticsMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : AnalyticsMessage) (rest : List UInt8) :
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
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end AnalyticsMessage

/-- Any Payload, selected by Message Type -/
inductive Payload where
  | loginRequestMessage (message : LoginRequestMessage) -- 1
  | replayRequestMessage (message : ReplayRequestMessage) -- 3
  | loginResponseMessage (message : LoginResponseMessage) -- 2
  | replayResponseMessage (message : ReplayResponseMessage) -- 4
  | replayAndRecoveryCompleteMessage (message : ReplayAndRecoveryCompleteMessage) -- 131
  | systemEventMessage (message : SystemEventMessage) -- 83
  | instrumentDirectoryMessage (message : InstrumentDirectoryMessage) -- 112
  | instrumentStatusMessage (message : InstrumentStatusMessage) -- 72
  | addOrderIncrementalMessage (message : AddOrderIncrementalMessage) -- 70
  | orderModifyMessage (message : OrderModifyMessage) -- 85
  | orderDeleteMessage (message : OrderDeleteMessage) -- 68
  | topOfBookMessage (message : TopOfBookMessage) -- 105
  | orderBookClearMessage (message : OrderBookClearMessage) -- 121
  | tradeMessage (message : TradeMessage) -- 80
  | tradeCrossMessage (message : TradeCrossMessage) -- 113
  | statisticsMessage (message : StatisticsMessage) -- 119
  | statisticsUpdateMessage (message : StatisticsUpdateMessage) -- 106
  | mifidIiTradeMessage (message : MifidIiTradeMessage) -- 81
  | miFidIiTradeCrossMessage (message : MiFidIiTradeCrossMessage) -- 86
  | tradeSummaryMessage (message : TradeSummaryMessage) -- 87
  | analyticsMessage (message : AnalyticsMessage) -- 97
  deriving DecidableEq, Repr

namespace Payload

/-- The Message Type each message is sent under -/
def tag : Payload → BitVec 8
  | .loginRequestMessage _ => 1
  | .replayRequestMessage _ => 3
  | .loginResponseMessage _ => 2
  | .replayResponseMessage _ => 4
  | .replayAndRecoveryCompleteMessage _ => 131
  | .systemEventMessage _ => 83
  | .instrumentDirectoryMessage _ => 112
  | .instrumentStatusMessage _ => 72
  | .addOrderIncrementalMessage _ => 70
  | .orderModifyMessage _ => 85
  | .orderDeleteMessage _ => 68
  | .topOfBookMessage _ => 105
  | .orderBookClearMessage _ => 121
  | .tradeMessage _ => 80
  | .tradeCrossMessage _ => 113
  | .statisticsMessage _ => 119
  | .statisticsUpdateMessage _ => 106
  | .mifidIiTradeMessage _ => 81
  | .miFidIiTradeCrossMessage _ => 86
  | .tradeSummaryMessage _ => 87
  | .analyticsMessage _ => 97

def encode : Payload → List UInt8
  | .loginRequestMessage message => LoginRequestMessage.encode message
  | .replayRequestMessage message => ReplayRequestMessage.encode message
  | .loginResponseMessage message => LoginResponseMessage.encode message
  | .replayResponseMessage message => ReplayResponseMessage.encode message
  | .replayAndRecoveryCompleteMessage message => ReplayAndRecoveryCompleteMessage.encode message
  | .systemEventMessage message => SystemEventMessage.encode message
  | .instrumentDirectoryMessage message => InstrumentDirectoryMessage.encode message
  | .instrumentStatusMessage message => InstrumentStatusMessage.encode message
  | .addOrderIncrementalMessage message => AddOrderIncrementalMessage.encode message
  | .orderModifyMessage message => OrderModifyMessage.encode message
  | .orderDeleteMessage message => OrderDeleteMessage.encode message
  | .topOfBookMessage message => TopOfBookMessage.encode message
  | .orderBookClearMessage message => OrderBookClearMessage.encode message
  | .tradeMessage message => TradeMessage.encode message
  | .tradeCrossMessage message => TradeCrossMessage.encode message
  | .statisticsMessage message => StatisticsMessage.encode message
  | .statisticsUpdateMessage message => StatisticsUpdateMessage.encode message
  | .mifidIiTradeMessage message => MifidIiTradeMessage.encode message
  | .miFidIiTradeCrossMessage message => MiFidIiTradeCrossMessage.encode message
  | .tradeSummaryMessage message => TradeSummaryMessage.encode message
  | .analyticsMessage message => AnalyticsMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : Payload) : (encode message).length ≤ 301 := by
  cases message with
  | loginRequestMessage inner =>
    simp only [encode, LoginRequestMessage.encode_length]
    omega
  | replayRequestMessage inner =>
    simp only [encode, ReplayRequestMessage.encode_length]
    omega
  | loginResponseMessage inner =>
    simp only [encode, LoginResponseMessage.encode_length]
    omega
  | replayResponseMessage inner =>
    simp only [encode, ReplayResponseMessage.encode_length]
    omega
  | replayAndRecoveryCompleteMessage inner =>
    simp only [encode, ReplayAndRecoveryCompleteMessage.encode_length]
    omega
  | systemEventMessage inner =>
    simp only [encode, SystemEventMessage.encode_length]
    omega
  | instrumentDirectoryMessage inner =>
    simp only [encode, InstrumentDirectoryMessage.encode_length]
    omega
  | instrumentStatusMessage inner =>
    simp only [encode, InstrumentStatusMessage.encode_length]
    omega
  | addOrderIncrementalMessage inner =>
    simp only [encode, AddOrderIncrementalMessage.encode_length]
    omega
  | orderModifyMessage inner =>
    simp only [encode, OrderModifyMessage.encode_length]
    omega
  | orderDeleteMessage inner =>
    simp only [encode, OrderDeleteMessage.encode_length]
    omega
  | topOfBookMessage inner =>
    simp only [encode, TopOfBookMessage.encode_length]
    omega
  | orderBookClearMessage inner =>
    simp only [encode, OrderBookClearMessage.encode_length]
    omega
  | tradeMessage inner =>
    simp only [encode, TradeMessage.encode_length]
    omega
  | tradeCrossMessage inner =>
    simp only [encode, TradeCrossMessage.encode_length]
    omega
  | statisticsMessage inner =>
    simp only [encode, StatisticsMessage.encode_length]
    omega
  | statisticsUpdateMessage inner =>
    simp only [encode, StatisticsUpdateMessage.encode_length]
    omega
  | mifidIiTradeMessage inner =>
    simp only [encode, MifidIiTradeMessage.encode_length]
    omega
  | miFidIiTradeCrossMessage inner =>
    simp only [encode, MiFidIiTradeCrossMessage.encode_length]
    omega
  | tradeSummaryMessage inner =>
    simp only [encode, TradeSummaryMessage.encode_length]
    omega
  | analyticsMessage inner =>
    simp only [encode, AnalyticsMessage.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (Payload × List UInt8) :=
  if tag = 1 then (LoginRequestMessage.decode bytes).map fun (message, rest) => (.loginRequestMessage message, rest)
  else if tag = 3 then (ReplayRequestMessage.decode bytes).map fun (message, rest) => (.replayRequestMessage message, rest)
  else if tag = 2 then (LoginResponseMessage.decode bytes).map fun (message, rest) => (.loginResponseMessage message, rest)
  else if tag = 4 then (ReplayResponseMessage.decode bytes).map fun (message, rest) => (.replayResponseMessage message, rest)
  else if tag = 131 then (ReplayAndRecoveryCompleteMessage.decode bytes).map fun (message, rest) => (.replayAndRecoveryCompleteMessage message, rest)
  else if tag = 83 then (SystemEventMessage.decode bytes).map fun (message, rest) => (.systemEventMessage message, rest)
  else if tag = 112 then (InstrumentDirectoryMessage.decode bytes).map fun (message, rest) => (.instrumentDirectoryMessage message, rest)
  else if tag = 72 then (InstrumentStatusMessage.decode bytes).map fun (message, rest) => (.instrumentStatusMessage message, rest)
  else if tag = 70 then (AddOrderIncrementalMessage.decode bytes).map fun (message, rest) => (.addOrderIncrementalMessage message, rest)
  else if tag = 85 then (OrderModifyMessage.decode bytes).map fun (message, rest) => (.orderModifyMessage message, rest)
  else if tag = 68 then (OrderDeleteMessage.decode bytes).map fun (message, rest) => (.orderDeleteMessage message, rest)
  else if tag = 105 then (TopOfBookMessage.decode bytes).map fun (message, rest) => (.topOfBookMessage message, rest)
  else if tag = 121 then (OrderBookClearMessage.decode bytes).map fun (message, rest) => (.orderBookClearMessage message, rest)
  else if tag = 80 then (TradeMessage.decode bytes).map fun (message, rest) => (.tradeMessage message, rest)
  else if tag = 113 then (TradeCrossMessage.decode bytes).map fun (message, rest) => (.tradeCrossMessage message, rest)
  else if tag = 119 then (StatisticsMessage.decode bytes).map fun (message, rest) => (.statisticsMessage message, rest)
  else if tag = 106 then (StatisticsUpdateMessage.decode bytes).map fun (message, rest) => (.statisticsUpdateMessage message, rest)
  else if tag = 81 then (MifidIiTradeMessage.decode bytes).map fun (message, rest) => (.mifidIiTradeMessage message, rest)
  else if tag = 86 then (MiFidIiTradeCrossMessage.decode bytes).map fun (message, rest) => (.miFidIiTradeCrossMessage message, rest)
  else if tag = 87 then (TradeSummaryMessage.decode bytes).map fun (message, rest) => (.tradeSummaryMessage message, rest)
  else if tag = 97 then (AnalyticsMessage.decode bytes).map fun (message, rest) => (.analyticsMessage message, rest)
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
  | loginRequestMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, LoginRequestMessage.encode_length]
    omega
  | replayRequestMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, ReplayRequestMessage.encode_length]
    omega
  | loginResponseMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, LoginResponseMessage.encode_length]
    omega
  | replayResponseMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, ReplayResponseMessage.encode_length]
    omega
  | replayAndRecoveryCompleteMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, ReplayAndRecoveryCompleteMessage.encode_length]
    omega
  | systemEventMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, SystemEventMessage.encode_length]
    omega
  | instrumentDirectoryMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, InstrumentDirectoryMessage.encode_length]
    omega
  | instrumentStatusMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, InstrumentStatusMessage.encode_length]
    omega
  | addOrderIncrementalMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, AddOrderIncrementalMessage.encode_length]
    omega
  | orderModifyMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, OrderModifyMessage.encode_length]
    omega
  | orderDeleteMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, OrderDeleteMessage.encode_length]
    omega
  | topOfBookMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, TopOfBookMessage.encode_length]
    omega
  | orderBookClearMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, OrderBookClearMessage.encode_length]
    omega
  | tradeMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, TradeMessage.encode_length]
    omega
  | tradeCrossMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, TradeCrossMessage.encode_length]
    omega
  | statisticsMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, StatisticsMessage.encode_length]
    omega
  | statisticsUpdateMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, StatisticsUpdateMessage.encode_length]
    omega
  | mifidIiTradeMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, MifidIiTradeMessage.encode_length]
    omega
  | miFidIiTradeCrossMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, MiFidIiTradeCrossMessage.encode_length]
    omega
  | tradeSummaryMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, TradeSummaryMessage.encode_length]
    omega
  | analyticsMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, AnalyticsMessage.encode_length]
    omega

/-- Size rule: Message Length counts the bytes after it plus 2, so it is written from the body and checked on decode -/
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

/-- Tcp Unit -/
structure TcpUnit where
  marketDataGroup : Alpha 1
  sequenceNumber : BitVec 32
  message : Bounded 1 Message
  deriving DecidableEq, Repr

namespace TcpUnit

def encodeBody (message : TcpUnit) : List UInt8 :=
  encodeUIntLE 1 (BitVec.ofNat (8 * 1) message.message.val.length)
    ++ (Alpha.encode message.marketDataGroup
    ++ (encodeUIntLE 4 message.sequenceNumber
    ++ (encodeMany Message.encode message.message.val)))

def decodeBody (bytes : List UInt8) : Option (TcpUnit × List UInt8) := do
  let (messageCount, bytes) ← decodeUIntLE 1 bytes
  let (marketDataGroup, bytes) ← Alpha.decode 1 bytes
  let (sequenceNumber, bytes) ← decodeUIntLE 4 bytes
  let (message_, bytes) ← decodeMany Message.decode messageCount.toNat bytes
  if fits_message : message_.length < 256 ^ 1 then
    pure ({ marketDataGroup, sequenceNumber, message := ⟨message_, fits_message⟩ }, bytes)
  else none

theorem decodeBody_encodeBody (message : TcpUnit) (rest : List UInt8) :
    decodeBody (encodeBody message ++ rest) = some (message, rest) := by
  unfold decodeBody encodeBody
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 Message.encode Message.decode Message.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.message.length_lt]
  rfl

/-- Size rule: Length counts the bytes after it plus 2, so it is written from the body; the body has no bound the prefix must fit, so it is read by its content and the prefix is not checked -/
def encode (message : TcpUnit) : List UInt8 :=
  encodeUIntLE 2 (BitVec.ofNat (8 * 2) ((encodeBody message).length + 2)) ++ encodeBody message

def decode (bytes : List UInt8) : Option (TcpUnit × List UInt8) := do
  let (_, bytes) ← decodeUIntLE 2 bytes
  decodeBody bytes

@[simp] theorem decode_encode (message : TcpUnit) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  exact decodeBody_encodeBody message rest

theorem encode_length_pos (message : TcpUnit) : (encode message).length > 0 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]
  omega

end TcpUnit

/-- Packet -/
structure Packet where
  tcpUnit : List TcpUnit
  deriving DecidableEq, Repr

namespace Packet

def encode (message : Packet) : List UInt8 :=
  encodeMany TcpUnit.encode message.tcpUnit

def decode (bytes : List UInt8) : Option Packet := do
  let tcpUnit ← decodeAll TcpUnit.decode bytes.length bytes
  pure { tcpUnit }

theorem decode_encode (message : Packet) : decode (encode message) = some message := by
  unfold decode encode
  rw [decodeAll_encodeMany TcpUnit.encode TcpUnit.decode TcpUnit.decode_encode TcpUnit.encode_length_pos message.tcpUnit _ (encodeMany_length_ge TcpUnit.encode TcpUnit.encode_length_pos message.tcpUnit), some_bind]
  rfl

end Packet

end Omi.LsegTurquoiseReplayGtpV244
