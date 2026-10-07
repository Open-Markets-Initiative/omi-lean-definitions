import Wire

/-!
# London Stock Exchange Level 2 MBO Recovery v26.2

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Note: Trade Flags is a bit field set, proven as its 1 byte integer rather than bit by bit.

Note: Allowed Book Types is a bit field set, proven as its 1 byte integer rather than bit by bit.

Note: Tcp Unit's Length is written from its body but not checked on decode, since the body has no bound the prefix must fit; the body is read by its content.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.LsegLseLevel2mborecoveryGtpV262

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

/-- Recovery Status: one byte code -/
def RecoveryStatus.codes : List UInt8 :=
  [0x41, 0x4F, 0x61, 0x62, 0x63, 0x64, 0x65]

inductive RecoveryStatus where
  | requestAccepted -- Request Accepted
  | outOfRange -- Out Of Range
  | invalidGroupOrInstrument -- Invalid Group Or Instrument
  | requestLimitReached -- Request Limit Reached
  | concurrentLimitReached -- Concurrent Limit Reached
  | invalidRecoveryTypeOrRequestLevel -- Invalid Recovery Type Or Request Level
  | failedOther -- Failed Other
  | unlisted (byte : { byte : UInt8 // byte ∉ RecoveryStatus.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace RecoveryStatus

def toByte : RecoveryStatus → UInt8
  | .requestAccepted => 0x41
  | .outOfRange => 0x4F
  | .invalidGroupOrInstrument => 0x61
  | .requestLimitReached => 0x62
  | .concurrentLimitReached => 0x63
  | .invalidRecoveryTypeOrRequestLevel => 0x64
  | .failedOther => 0x65
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : RecoveryStatus :=
  if byte = 0x41 then .requestAccepted
  else if byte = 0x4F then .outOfRange
  else if byte = 0x61 then .invalidGroupOrInstrument
  else if byte = 0x62 then .requestLimitReached
  else if byte = 0x63 then .concurrentLimitReached
  else if byte = 0x64 then .invalidRecoveryTypeOrRequestLevel
  else .failedOther

def ofByte (byte : UInt8) : RecoveryStatus :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : RecoveryStatus) : ofByte value.toByte = value := by
  cases value with
  | requestAccepted => decide
  | outOfRange => decide
  | invalidGroupOrInstrument => decide
  | requestLimitReached => decide
  | concurrentLimitReached => decide
  | invalidRecoveryTypeOrRequestLevel => decide
  | failedOther => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : RecoveryStatus) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (RecoveryStatus × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : RecoveryStatus) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : RecoveryStatus) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end RecoveryStatus

/-- Trading Status: one byte code -/
def TradingStatus.codes : List UInt8 :=
  [0x48, 0x4A, 0x4B, 0x54, 0x50, 0x74, 0x61, 0x62, 0x63, 0x64, 0x65, 0x66, 0x6D, 0x6E, 0x6F, 0x71, 0x72, 0x31, 0x32, 0x77, 0x78, 0x75]

inductive TradingStatus where
  | halt -- Halt
  | haltMatchingPartitionSuspended -- Halt Matching Partition Suspended
  | haltSystemSuspended -- Halt System Suspended
  | regularTradingStartTradeReporting -- Regular Trading Start Trade Reporting
  | haltRegulatory -- Halt Regulatory
  | endTradeReporting -- End Trade Reporting
  | openingAuctionCall -- Opening Auction Call
  | postClose -- Post Close
  | closed -- Closed
  | closingAuctionCall -- Closing Auction Call
  | aespAuctionCall -- Aesp Auction Call
  | resumeAuction -- Resume Auction
  | preMandatory -- Pre Mandatory
  | mandatory -- Mandatory
  | postMandatory -- Post Mandatory
  | edspAuctionCall -- Edsp Auction Call
  | periodicAuctionCall -- Periodic Auction Call
  | inactive -- Inactive
  | suspended -- Suspended
  | noActiveSession -- No Active Session
  | endOfPostClose -- End Of Post Close
  | closingPriceCrossingSession -- Closing Price Crossing Session
  | unlisted (byte : { byte : UInt8 // byte ∉ TradingStatus.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TradingStatus

def toByte : TradingStatus → UInt8
  | .halt => 0x48
  | .haltMatchingPartitionSuspended => 0x4A
  | .haltSystemSuspended => 0x4B
  | .regularTradingStartTradeReporting => 0x54
  | .haltRegulatory => 0x50
  | .endTradeReporting => 0x74
  | .openingAuctionCall => 0x61
  | .postClose => 0x62
  | .closed => 0x63
  | .closingAuctionCall => 0x64
  | .aespAuctionCall => 0x65
  | .resumeAuction => 0x66
  | .preMandatory => 0x6D
  | .mandatory => 0x6E
  | .postMandatory => 0x6F
  | .edspAuctionCall => 0x71
  | .periodicAuctionCall => 0x72
  | .inactive => 0x31
  | .suspended => 0x32
  | .noActiveSession => 0x77
  | .endOfPostClose => 0x78
  | .closingPriceCrossingSession => 0x75
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TradingStatus :=
  if byte = 0x48 then .halt
  else if byte = 0x4A then .haltMatchingPartitionSuspended
  else if byte = 0x4B then .haltSystemSuspended
  else if byte = 0x54 then .regularTradingStartTradeReporting
  else if byte = 0x50 then .haltRegulatory
  else if byte = 0x74 then .endTradeReporting
  else if byte = 0x61 then .openingAuctionCall
  else if byte = 0x62 then .postClose
  else if byte = 0x63 then .closed
  else if byte = 0x64 then .closingAuctionCall
  else if byte = 0x65 then .aespAuctionCall
  else if byte = 0x66 then .resumeAuction
  else if byte = 0x6D then .preMandatory
  else if byte = 0x6E then .mandatory
  else if byte = 0x6F then .postMandatory
  else if byte = 0x71 then .edspAuctionCall
  else if byte = 0x72 then .periodicAuctionCall
  else if byte = 0x31 then .inactive
  else if byte = 0x32 then .suspended
  else if byte = 0x77 then .noActiveSession
  else if byte = 0x78 then .endOfPostClose
  else .closingPriceCrossingSession

def ofByte (byte : UInt8) : TradingStatus :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TradingStatus) : ofByte value.toByte = value := by
  cases value with
  | halt => decide
  | haltMatchingPartitionSuspended => decide
  | haltSystemSuspended => decide
  | regularTradingStartTradeReporting => decide
  | haltRegulatory => decide
  | endTradeReporting => decide
  | openingAuctionCall => decide
  | postClose => decide
  | closed => decide
  | closingAuctionCall => decide
  | aespAuctionCall => decide
  | resumeAuction => decide
  | preMandatory => decide
  | mandatory => decide
  | postMandatory => decide
  | edspAuctionCall => decide
  | periodicAuctionCall => decide
  | inactive => decide
  | suspended => decide
  | noActiveSession => decide
  | endOfPostClose => decide
  | closingPriceCrossingSession => decide
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

/-- Side: one byte code -/
def Side.codes : List UInt8 :=
  [0x42, 0x53]

inductive Side where
  | buyOrder -- Buy Order
  | sellOrder -- Sell Order
  | unlisted (byte : { byte : UInt8 // byte ∉ Side.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Side

def toByte : Side → UInt8
  | .buyOrder => 0x42
  | .sellOrder => 0x53
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Side :=
  if byte = 0x42 then .buyOrder
  else .sellOrder

def ofByte (byte : UInt8) : Side :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Side) : ofByte value.toByte = value := by
  cases value with
  | buyOrder => decide
  | sellOrder => decide
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

/-- Auction Type: one byte code -/
def AuctionType.codes : List UInt8 :=
  [0x43, 0x4F, 0x41, 0x42, 0x45, 0x46]

inductive AuctionType where
  | closingAuction -- Closing Auction
  | openingAuction -- Opening Auction
  | aesp -- Aesp
  | edsp -- Edsp
  | resumeAuction -- Resume Auction
  | periodicAuction -- Periodic Auction
  | unlisted (byte : { byte : UInt8 // byte ∉ AuctionType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace AuctionType

def toByte : AuctionType → UInt8
  | .closingAuction => 0x43
  | .openingAuction => 0x4F
  | .aesp => 0x41
  | .edsp => 0x42
  | .resumeAuction => 0x45
  | .periodicAuction => 0x46
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : AuctionType :=
  if byte = 0x43 then .closingAuction
  else if byte = 0x4F then .openingAuction
  else if byte = 0x41 then .aesp
  else if byte = 0x42 then .edsp
  else if byte = 0x45 then .resumeAuction
  else .periodicAuction

def ofByte (byte : UInt8) : AuctionType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : AuctionType) : ofByte value.toByte = value := by
  cases value with
  | closingAuction => decide
  | openingAuction => decide
  | aesp => decide
  | edsp => decide
  | resumeAuction => decide
  | periodicAuction => decide
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
  [0x20, 0x43]

inductive TradeQualifier where
  | na -- Na
  | closingPriceCrossCpx -- Closing Price Cross Cpx
  | unlisted (byte : { byte : UInt8 // byte ∉ TradeQualifier.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TradeQualifier

def toByte : TradeQualifier → UInt8
  | .na => 0x20
  | .closingPriceCrossCpx => 0x43
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TradeQualifier :=
  if byte = 0x20 then .na
  else .closingPriceCrossCpx

def ofByte (byte : UInt8) : TradeQualifier :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TradeQualifier) : ofByte value.toByte = value := by
  cases value with
  | na => decide
  | closingPriceCrossCpx => decide
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

/-- Opening Price Indicator: one byte code -/
def OpeningPriceIndicator.codes : List UInt8 :=
  [0x41, 0x42, 0x43, 0x44, 0x45, 0x46, 0x49]

inductive OpeningPriceIndicator where
  | ut -- Ut
  | at_ -- At
  | midOfBbo -- Mid Of Bbo
  | lastAt -- Last At
  | lastUt -- Last Ut
  | manual -- Manual
  | previousClose -- Previous Close
  | unlisted (byte : { byte : UInt8 // byte ∉ OpeningPriceIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OpeningPriceIndicator

def toByte : OpeningPriceIndicator → UInt8
  | .ut => 0x41
  | .at_ => 0x42
  | .midOfBbo => 0x43
  | .lastAt => 0x44
  | .lastUt => 0x45
  | .manual => 0x46
  | .previousClose => 0x49
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OpeningPriceIndicator :=
  if byte = 0x41 then .ut
  else if byte = 0x42 then .at_
  else if byte = 0x43 then .midOfBbo
  else if byte = 0x44 then .lastAt
  else if byte = 0x45 then .lastUt
  else if byte = 0x46 then .manual
  else .previousClose

def ofByte (byte : UInt8) : OpeningPriceIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OpeningPriceIndicator) : ofByte value.toByte = value := by
  cases value with
  | ut => decide
  | at_ => decide
  | midOfBbo => decide
  | lastAt => decide
  | lastUt => decide
  | manual => decide
  | previousClose => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : OpeningPriceIndicator) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (OpeningPriceIndicator × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : OpeningPriceIndicator) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : OpeningPriceIndicator) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end OpeningPriceIndicator

/-- Closing Price Indicator: one byte code -/
def ClosingPriceIndicator.codes : List UInt8 :=
  [0x41, 0x42, 0x43, 0x44, 0x45, 0x46, 0x49]

inductive ClosingPriceIndicator where
  | ut -- Ut
  | at_ -- At
  | midOfBbo -- Mid Of Bbo
  | lastAt -- Last At
  | lastUt -- Last Ut
  | manual -- Manual
  | previousClose -- Previous Close
  | unlisted (byte : { byte : UInt8 // byte ∉ ClosingPriceIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ClosingPriceIndicator

def toByte : ClosingPriceIndicator → UInt8
  | .ut => 0x41
  | .at_ => 0x42
  | .midOfBbo => 0x43
  | .lastAt => 0x44
  | .lastUt => 0x45
  | .manual => 0x46
  | .previousClose => 0x49
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ClosingPriceIndicator :=
  if byte = 0x41 then .ut
  else if byte = 0x42 then .at_
  else if byte = 0x43 then .midOfBbo
  else if byte = 0x44 then .lastAt
  else if byte = 0x45 then .lastUt
  else if byte = 0x46 then .manual
  else .previousClose

def ofByte (byte : UInt8) : ClosingPriceIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ClosingPriceIndicator) : ofByte value.toByte = value := by
  cases value with
  | ut => decide
  | at_ => decide
  | midOfBbo => decide
  | lastAt => decide
  | lastUt => decide
  | manual => decide
  | previousClose => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ClosingPriceIndicator) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ClosingPriceIndicator × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ClosingPriceIndicator) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : ClosingPriceIndicator) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ClosingPriceIndicator

/-- Imbalance Direction: one byte code -/
def ImbalanceDirection.codes : List UInt8 :=
  [0x42, 0x4E, 0x4F, 0x53]

inductive ImbalanceDirection where
  | buyImbalance -- Buy Imbalance
  | noImbalance -- No Imbalance
  | insufficientOrdersForAuction -- Insufficient Orders For Auction
  | sellImbalance -- Sell Imbalance
  | unlisted (byte : { byte : UInt8 // byte ∉ ImbalanceDirection.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ImbalanceDirection

def toByte : ImbalanceDirection → UInt8
  | .buyImbalance => 0x42
  | .noImbalance => 0x4E
  | .insufficientOrdersForAuction => 0x4F
  | .sellImbalance => 0x53
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ImbalanceDirection :=
  if byte = 0x42 then .buyImbalance
  else if byte = 0x4E then .noImbalance
  else if byte = 0x4F then .insufficientOrdersForAuction
  else .sellImbalance

def ofByte (byte : UInt8) : ImbalanceDirection :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ImbalanceDirection) : ofByte value.toByte = value := by
  cases value with
  | buyImbalance => decide
  | noImbalance => decide
  | insufficientOrdersForAuction => decide
  | sellImbalance => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ImbalanceDirection) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ImbalanceDirection × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ImbalanceDirection) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : ImbalanceDirection) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ImbalanceDirection

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

/-- Recovery Request Message: 27 bytes -/
structure RecoveryRequestMessage where
  requestLevel : BitVec 8
  instrument : BitVec 64
  groupId : Alpha 6
  requestOrderBookType : BitVec 8
  sourceVenue : BitVec 16
  recoveryType : BitVec 8
  sequenceNumber : BitVec 32
  requestId : BitVec 32
  deriving DecidableEq, Repr

namespace RecoveryRequestMessage

def encode (message : RecoveryRequestMessage) : List UInt8 :=
  encodeUIntLE 1 message.requestLevel
    ++ (encodeUIntLE 8 message.instrument
    ++ (Alpha.encode message.groupId
    ++ (encodeUIntLE 1 message.requestOrderBookType
    ++ (encodeUIntLE 2 message.sourceVenue
    ++ (encodeUIntLE 1 message.recoveryType
    ++ (encodeUIntLE 4 message.sequenceNumber
    ++ (encodeUIntLE 4 message.requestId)))))))

def decode (bytes : List UInt8) : Option (RecoveryRequestMessage × List UInt8) := do
  let (requestLevel, bytes) ← decodeUIntLE 1 bytes
  let (instrument, bytes) ← decodeUIntLE 8 bytes
  let (groupId, bytes) ← Alpha.decode 6 bytes
  let (requestOrderBookType, bytes) ← decodeUIntLE 1 bytes
  let (sourceVenue, bytes) ← decodeUIntLE 2 bytes
  let (recoveryType, bytes) ← decodeUIntLE 1 bytes
  let (sequenceNumber, bytes) ← decodeUIntLE 4 bytes
  let (requestId, bytes) ← decodeUIntLE 4 bytes
  pure ({ requestLevel, instrument, groupId, requestOrderBookType, sourceVenue, recoveryType, sequenceNumber, requestId }, bytes)

@[simp] theorem encode_length (message : RecoveryRequestMessage) : (encode message).length = 27 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : RecoveryRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : RecoveryRequestMessage) (rest : List UInt8) :
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
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end RecoveryRequestMessage

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

/-- Recovery Response Message: 13 bytes -/
structure RecoveryResponseMessage where
  sequenceNumber : BitVec 32
  count : BitVec 32
  recoveryStatus : RecoveryStatus
  requestId : BitVec 32
  deriving DecidableEq, Repr

namespace RecoveryResponseMessage

def encode (message : RecoveryResponseMessage) : List UInt8 :=
  encodeUIntLE 4 message.sequenceNumber
    ++ (encodeUIntLE 4 message.count
    ++ (RecoveryStatus.encode message.recoveryStatus
    ++ (encodeUIntLE 4 message.requestId)))

def decode (bytes : List UInt8) : Option (RecoveryResponseMessage × List UInt8) := do
  let (sequenceNumber, bytes) ← decodeUIntLE 4 bytes
  let (count, bytes) ← decodeUIntLE 4 bytes
  let (recoveryStatus, bytes) ← RecoveryStatus.decode bytes
  let (requestId, bytes) ← decodeUIntLE 4 bytes
  pure ({ sequenceNumber, count, recoveryStatus, requestId }, bytes)

@[simp] theorem encode_length (message : RecoveryResponseMessage) : (encode message).length = 13 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, RecoveryStatus.encode_length]

theorem encode_length_pos (message : RecoveryResponseMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : RecoveryResponseMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, RecoveryStatus.decode_encode, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end RecoveryResponseMessage

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

/-- Add Order Mbo Message: 64 bytes -/
structure AddOrderMboMessage where
  timestamp : BitVec 64
  orderId : BitVec 64
  side : Side
  size : BitVec 64
  instrument : BitVec 64
  price : BitVec 64
  reserved8 : Alpha 8
  sourceVenue : BitVec 16
  orderBookType : BitVec 8
  participant : Alpha 11
  depth : BitVec 8
  deriving DecidableEq, Repr

namespace AddOrderMboMessage

def encode (message : AddOrderMboMessage) : List UInt8 :=
  encodeUIntLE 8 message.timestamp
    ++ (encodeUIntLE 8 message.orderId
    ++ (Side.encode message.side
    ++ (encodeUIntLE 8 message.size
    ++ (encodeUIntLE 8 message.instrument
    ++ (encodeUIntLE 8 message.price
    ++ (Alpha.encode message.reserved8
    ++ (encodeUIntLE 2 message.sourceVenue
    ++ (encodeUIntLE 1 message.orderBookType
    ++ (Alpha.encode message.participant
    ++ (encodeUIntLE 1 message.depth))))))))))

def decode (bytes : List UInt8) : Option (AddOrderMboMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (side, bytes) ← Side.decode bytes
  let (size, bytes) ← decodeUIntLE 8 bytes
  let (instrument, bytes) ← decodeUIntLE 8 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (reserved8, bytes) ← Alpha.decode 8 bytes
  let (sourceVenue, bytes) ← decodeUIntLE 2 bytes
  let (orderBookType, bytes) ← decodeUIntLE 1 bytes
  let (participant, bytes) ← Alpha.decode 11 bytes
  let (depth, bytes) ← decodeUIntLE 1 bytes
  pure ({ timestamp, orderId, side, size, instrument, price, reserved8, sourceVenue, orderBookType, participant, depth }, bytes)

@[simp] theorem encode_length (message : AddOrderMboMessage) : (encode message).length = 64 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Side.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : AddOrderMboMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : AddOrderMboMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end AddOrderMboMessage

/-- Add Order Short Mbo Message: 43 bytes -/
structure AddOrderShortMboMessage where
  orderId : BitVec 64
  size : BitVec 64
  price : BitVec 64
  reserved8 : Alpha 8
  participant : Alpha 11
  deriving DecidableEq, Repr

namespace AddOrderShortMboMessage

def encode (message : AddOrderShortMboMessage) : List UInt8 :=
  encodeUIntLE 8 message.orderId
    ++ (encodeUIntLE 8 message.size
    ++ (encodeUIntLE 8 message.price
    ++ (Alpha.encode message.reserved8
    ++ (Alpha.encode message.participant))))

def decode (bytes : List UInt8) : Option (AddOrderShortMboMessage × List UInt8) := do
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (size, bytes) ← decodeUIntLE 8 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (reserved8, bytes) ← Alpha.decode 8 bytes
  let (participant, bytes) ← Alpha.decode 11 bytes
  pure ({ orderId, size, price, reserved8, participant }, bytes)

@[simp] theorem encode_length (message : AddOrderShortMboMessage) : (encode message).length = 43 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : AddOrderShortMboMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : AddOrderShortMboMessage) (rest : List UInt8) :
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
  rw [Alpha.decode_encode, some_bind]
  rfl

end AddOrderShortMboMessage

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

/-- Instrument Directory Equities Message: 310 bytes -/
structure InstrumentDirectoryEquitiesMessage where
  timestamp : BitVec 64
  instrument : BitVec 64
  isin : Alpha 12
  sedol : Alpha 8
  allowedBookTypes : BitVec 8
  sourceVenue : BitVec 16
  venueInstrumentId : Alpha 11
  segment : Alpha 6
  currency : Alpha 3
  tickId : Alpha 2
  previousDaysClosingPrice : BitVec 64
  reserved8 : Alpha 8
  dynamicCircuitBreakerTolerances : BitVec 64
  staticCircuitBreakerTolerances : BitVec 64
  firstReserved1 : Alpha 1
  secondReserved1 : Alpha 1
  expirationDate : Alpha 8
  listingStartDate : Alpha 8
  listingEndDate : Alpha 8
  minimumLotMinimumExecutionSize : BitVec 64
  lastPriceInPrecedingSession : BitVec 64
  lastPriceInPrecedingSessionDate : Alpha 8
  thirdReserved1 : Alpha 1
  secondReserved8 : Alpha 8
  thirdReserved8 : Alpha 8
  exMarkerCode : Alpha 2
  securityType : BitVec 8
  countryOfRegister : Alpha 3
  exchangeMarketSize : BitVec 64
  minimumPeakSizeMultiplier : BitVec 64
  securityMaximumSpread : BitVec 64
  clearingType : BitVec 8
  strikePrice : BitVec 64
  securityExchange : Alpha 11
  reserved12 : Alpha 12
  reserved1 : Alpha 1
  fourthReserved8 : Alpha 8
  fifthReserved8 : Alpha 8
  partitionId : Alpha 1
  sixthReserved8 : Alpha 8
  seventhReserved8 : Alpha 8
  reserved4 : Alpha 4
  reserved2 : Alpha 2
  symbol : Alpha 8
  description : Alpha 40
  deriving DecidableEq, Repr

namespace InstrumentDirectoryEquitiesMessage

def encode (message : InstrumentDirectoryEquitiesMessage) : List UInt8 :=
  encodeUIntLE 8 message.timestamp
    ++ (encodeUIntLE 8 message.instrument
    ++ (Alpha.encode message.isin
    ++ (Alpha.encode message.sedol
    ++ (encodeUIntLE 1 message.allowedBookTypes
    ++ (encodeUIntLE 2 message.sourceVenue
    ++ (Alpha.encode message.venueInstrumentId
    ++ (Alpha.encode message.segment
    ++ (Alpha.encode message.currency
    ++ (Alpha.encode message.tickId
    ++ (encodeUIntLE 8 message.previousDaysClosingPrice
    ++ (Alpha.encode message.reserved8
    ++ (encodeUIntLE 8 message.dynamicCircuitBreakerTolerances
    ++ (encodeUIntLE 8 message.staticCircuitBreakerTolerances
    ++ (Alpha.encode message.firstReserved1
    ++ (Alpha.encode message.secondReserved1
    ++ (Alpha.encode message.expirationDate
    ++ (Alpha.encode message.listingStartDate
    ++ (Alpha.encode message.listingEndDate
    ++ (encodeUIntLE 8 message.minimumLotMinimumExecutionSize
    ++ (encodeUIntLE 8 message.lastPriceInPrecedingSession
    ++ (Alpha.encode message.lastPriceInPrecedingSessionDate
    ++ (Alpha.encode message.thirdReserved1
    ++ (Alpha.encode message.secondReserved8
    ++ (Alpha.encode message.thirdReserved8
    ++ (Alpha.encode message.exMarkerCode
    ++ (encodeUIntLE 1 message.securityType
    ++ (Alpha.encode message.countryOfRegister
    ++ (encodeUIntLE 8 message.exchangeMarketSize
    ++ (encodeUIntLE 8 message.minimumPeakSizeMultiplier
    ++ (encodeUIntLE 8 message.securityMaximumSpread
    ++ (encodeUIntLE 1 message.clearingType
    ++ (encodeUIntLE 8 message.strikePrice
    ++ (Alpha.encode message.securityExchange
    ++ (Alpha.encode message.reserved12
    ++ (Alpha.encode message.reserved1
    ++ (Alpha.encode message.fourthReserved8
    ++ (Alpha.encode message.fifthReserved8
    ++ (Alpha.encode message.partitionId
    ++ (Alpha.encode message.sixthReserved8
    ++ (Alpha.encode message.seventhReserved8
    ++ (Alpha.encode message.reserved4
    ++ (Alpha.encode message.reserved2
    ++ (Alpha.encode message.symbol
    ++ (Alpha.encode message.description))))))))))))))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (InstrumentDirectoryEquitiesMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  let (instrument, bytes) ← decodeUIntLE 8 bytes
  let (isin, bytes) ← Alpha.decode 12 bytes
  let (sedol, bytes) ← Alpha.decode 8 bytes
  let (allowedBookTypes, bytes) ← decodeUIntLE 1 bytes
  let (sourceVenue, bytes) ← decodeUIntLE 2 bytes
  let (venueInstrumentId, bytes) ← Alpha.decode 11 bytes
  let (segment, bytes) ← Alpha.decode 6 bytes
  let (currency, bytes) ← Alpha.decode 3 bytes
  let (tickId, bytes) ← Alpha.decode 2 bytes
  let (previousDaysClosingPrice, bytes) ← decodeUIntLE 8 bytes
  let (reserved8, bytes) ← Alpha.decode 8 bytes
  let (dynamicCircuitBreakerTolerances, bytes) ← decodeUIntLE 8 bytes
  let (staticCircuitBreakerTolerances, bytes) ← decodeUIntLE 8 bytes
  let (firstReserved1, bytes) ← Alpha.decode 1 bytes
  let (secondReserved1, bytes) ← Alpha.decode 1 bytes
  let (expirationDate, bytes) ← Alpha.decode 8 bytes
  let (listingStartDate, bytes) ← Alpha.decode 8 bytes
  let (listingEndDate, bytes) ← Alpha.decode 8 bytes
  let (minimumLotMinimumExecutionSize, bytes) ← decodeUIntLE 8 bytes
  let (lastPriceInPrecedingSession, bytes) ← decodeUIntLE 8 bytes
  let (lastPriceInPrecedingSessionDate, bytes) ← Alpha.decode 8 bytes
  let (thirdReserved1, bytes) ← Alpha.decode 1 bytes
  let (secondReserved8, bytes) ← Alpha.decode 8 bytes
  let (thirdReserved8, bytes) ← Alpha.decode 8 bytes
  let (exMarkerCode, bytes) ← Alpha.decode 2 bytes
  let (securityType, bytes) ← decodeUIntLE 1 bytes
  let (countryOfRegister, bytes) ← Alpha.decode 3 bytes
  let (exchangeMarketSize, bytes) ← decodeUIntLE 8 bytes
  let (minimumPeakSizeMultiplier, bytes) ← decodeUIntLE 8 bytes
  let (securityMaximumSpread, bytes) ← decodeUIntLE 8 bytes
  let (clearingType, bytes) ← decodeUIntLE 1 bytes
  let (strikePrice, bytes) ← decodeUIntLE 8 bytes
  let (securityExchange, bytes) ← Alpha.decode 11 bytes
  let (reserved12, bytes) ← Alpha.decode 12 bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  let (fourthReserved8, bytes) ← Alpha.decode 8 bytes
  let (fifthReserved8, bytes) ← Alpha.decode 8 bytes
  let (partitionId, bytes) ← Alpha.decode 1 bytes
  let (sixthReserved8, bytes) ← Alpha.decode 8 bytes
  let (seventhReserved8, bytes) ← Alpha.decode 8 bytes
  let (reserved4, bytes) ← Alpha.decode 4 bytes
  let (reserved2, bytes) ← Alpha.decode 2 bytes
  let (symbol, bytes) ← Alpha.decode 8 bytes
  let (description, bytes) ← Alpha.decode 40 bytes
  pure ({ timestamp, instrument, isin, sedol, allowedBookTypes, sourceVenue, venueInstrumentId, segment, currency, tickId, previousDaysClosingPrice, reserved8, dynamicCircuitBreakerTolerances, staticCircuitBreakerTolerances, firstReserved1, secondReserved1, expirationDate, listingStartDate, listingEndDate, minimumLotMinimumExecutionSize, lastPriceInPrecedingSession, lastPriceInPrecedingSessionDate, thirdReserved1, secondReserved8, thirdReserved8, exMarkerCode, securityType, countryOfRegister, exchangeMarketSize, minimumPeakSizeMultiplier, securityMaximumSpread, clearingType, strikePrice, securityExchange, reserved12, reserved1, fourthReserved8, fifthReserved8, partitionId, sixthReserved8, seventhReserved8, reserved4, reserved2, symbol, description }, bytes)

@[simp] theorem encode_length (message : InstrumentDirectoryEquitiesMessage) : (encode message).length = 310 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : InstrumentDirectoryEquitiesMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : InstrumentDirectoryEquitiesMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
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
  rw [Alpha.decode_encode, some_bind]
  rfl

end InstrumentDirectoryEquitiesMessage

/-- Statistics Snapshot Message: 270 bytes -/
structure StatisticsSnapshotMessage where
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
  officialOpeningPrice : BitVec 64
  officialClosingPrice : BitVec 64
  tradeHighOnbookOnly : BitVec 64
  tradeLowOnbookOnly : BitVec 64
  tradeHigh : BitVec 64
  tradeLow : BitVec 64
  fiftyTwoWeekTradeHigh : BitVec 64
  fiftyTwoWeekTradeLow : BitVec 64
  openingPriceIndicator : OpeningPriceIndicator
  closingPriceIndicator : ClosingPriceIndicator
  iauPrice : BitVec 64
  iauPairedSize : BitVec 64
  imbalanceQuantity : BitVec 64
  imbalanceDirection : ImbalanceDirection
  bestClosingBidPrice : BitVec 64
  bestClosingAskPrice : BitVec 64
  bestClosingBidSize : BitVec 64
  bestClosingAskSize : BitVec 64
  reserved8 : Alpha 8
  secondReserved8 : Alpha 8
  thirdReserved8 : Alpha 8
  fourthReserved8 : Alpha 8
  auctionType : AuctionType
  lastTradePrice : BitVec 64
  lastTradeQuantity : BitVec 64
  lastTradeTime : BitVec 64
  staticReferencePrice : BitVec 64
  dynamicReferencePrice : BitVec 64
  deriving DecidableEq, Repr

namespace StatisticsSnapshotMessage

def encode (message : StatisticsSnapshotMessage) : List UInt8 :=
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
    ++ (encodeUIntLE 8 message.turnoverOnbookOnly
    ++ (encodeUIntLE 8 message.officialOpeningPrice
    ++ (encodeUIntLE 8 message.officialClosingPrice
    ++ (encodeUIntLE 8 message.tradeHighOnbookOnly
    ++ (encodeUIntLE 8 message.tradeLowOnbookOnly
    ++ (encodeUIntLE 8 message.tradeHigh
    ++ (encodeUIntLE 8 message.tradeLow
    ++ (encodeUIntLE 8 message.fiftyTwoWeekTradeHigh
    ++ (encodeUIntLE 8 message.fiftyTwoWeekTradeLow
    ++ (OpeningPriceIndicator.encode message.openingPriceIndicator
    ++ (ClosingPriceIndicator.encode message.closingPriceIndicator
    ++ (encodeUIntLE 8 message.iauPrice
    ++ (encodeUIntLE 8 message.iauPairedSize
    ++ (encodeUIntLE 8 message.imbalanceQuantity
    ++ (ImbalanceDirection.encode message.imbalanceDirection
    ++ (encodeUIntLE 8 message.bestClosingBidPrice
    ++ (encodeUIntLE 8 message.bestClosingAskPrice
    ++ (encodeUIntLE 8 message.bestClosingBidSize
    ++ (encodeUIntLE 8 message.bestClosingAskSize
    ++ (Alpha.encode message.reserved8
    ++ (Alpha.encode message.secondReserved8
    ++ (Alpha.encode message.thirdReserved8
    ++ (Alpha.encode message.fourthReserved8
    ++ (AuctionType.encode message.auctionType
    ++ (encodeUIntLE 8 message.lastTradePrice
    ++ (encodeUIntLE 8 message.lastTradeQuantity
    ++ (encodeUIntLE 8 message.lastTradeTime
    ++ (encodeUIntLE 8 message.staticReferencePrice
    ++ (encodeUIntLE 8 message.dynamicReferencePrice))))))))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (StatisticsSnapshotMessage × List UInt8) := do
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
  let (officialOpeningPrice, bytes) ← decodeUIntLE 8 bytes
  let (officialClosingPrice, bytes) ← decodeUIntLE 8 bytes
  let (tradeHighOnbookOnly, bytes) ← decodeUIntLE 8 bytes
  let (tradeLowOnbookOnly, bytes) ← decodeUIntLE 8 bytes
  let (tradeHigh, bytes) ← decodeUIntLE 8 bytes
  let (tradeLow, bytes) ← decodeUIntLE 8 bytes
  let (fiftyTwoWeekTradeHigh, bytes) ← decodeUIntLE 8 bytes
  let (fiftyTwoWeekTradeLow, bytes) ← decodeUIntLE 8 bytes
  let (openingPriceIndicator, bytes) ← OpeningPriceIndicator.decode bytes
  let (closingPriceIndicator, bytes) ← ClosingPriceIndicator.decode bytes
  let (iauPrice, bytes) ← decodeUIntLE 8 bytes
  let (iauPairedSize, bytes) ← decodeUIntLE 8 bytes
  let (imbalanceQuantity, bytes) ← decodeUIntLE 8 bytes
  let (imbalanceDirection, bytes) ← ImbalanceDirection.decode bytes
  let (bestClosingBidPrice, bytes) ← decodeUIntLE 8 bytes
  let (bestClosingAskPrice, bytes) ← decodeUIntLE 8 bytes
  let (bestClosingBidSize, bytes) ← decodeUIntLE 8 bytes
  let (bestClosingAskSize, bytes) ← decodeUIntLE 8 bytes
  let (reserved8, bytes) ← Alpha.decode 8 bytes
  let (secondReserved8, bytes) ← Alpha.decode 8 bytes
  let (thirdReserved8, bytes) ← Alpha.decode 8 bytes
  let (fourthReserved8, bytes) ← Alpha.decode 8 bytes
  let (auctionType, bytes) ← AuctionType.decode bytes
  let (lastTradePrice, bytes) ← decodeUIntLE 8 bytes
  let (lastTradeQuantity, bytes) ← decodeUIntLE 8 bytes
  let (lastTradeTime, bytes) ← decodeUIntLE 8 bytes
  let (staticReferencePrice, bytes) ← decodeUIntLE 8 bytes
  let (dynamicReferencePrice, bytes) ← decodeUIntLE 8 bytes
  pure ({ timestamp, instrument, sourceVenue, volume, volumeOnbookOnly, vwap, vwapOnbookOnly, numberOfTrades, numberOfTradesOnbookOnly, turnover, turnoverOnbookOnly, officialOpeningPrice, officialClosingPrice, tradeHighOnbookOnly, tradeLowOnbookOnly, tradeHigh, tradeLow, fiftyTwoWeekTradeHigh, fiftyTwoWeekTradeLow, openingPriceIndicator, closingPriceIndicator, iauPrice, iauPairedSize, imbalanceQuantity, imbalanceDirection, bestClosingBidPrice, bestClosingAskPrice, bestClosingBidSize, bestClosingAskSize, reserved8, secondReserved8, thirdReserved8, fourthReserved8, auctionType, lastTradePrice, lastTradeQuantity, lastTradeTime, staticReferencePrice, dynamicReferencePrice }, bytes)

@[simp] theorem encode_length (message : StatisticsSnapshotMessage) : (encode message).length = 270 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, OpeningPriceIndicator.encode_length, ClosingPriceIndicator.encode_length, ImbalanceDirection.encode_length, Alpha.encode_length, AuctionType.encode_length]

theorem encode_length_pos (message : StatisticsSnapshotMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : StatisticsSnapshotMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, OpeningPriceIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ClosingPriceIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, ImbalanceDirection.decode_encode, some_bind]
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, AuctionType.decode_encode, some_bind]
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

end StatisticsSnapshotMessage

/-- Any Payload, selected by Message Type -/
inductive Payload where
  | loginRequestMessage (message : LoginRequestMessage) -- 1
  | recoveryRequestMessage (message : RecoveryRequestMessage) -- 129
  | loginResponseMessage (message : LoginResponseMessage) -- 2
  | recoveryResponseMessage (message : RecoveryResponseMessage) -- 130
  | replayAndRecoveryCompleteMessage (message : ReplayAndRecoveryCompleteMessage) -- 131
  | systemEventMessage (message : SystemEventMessage) -- 83
  | instrumentStatusMessage (message : InstrumentStatusMessage) -- 72
  | addOrderMboMessage (message : AddOrderMboMessage) -- 65
  | addOrderShortMboMessage (message : AddOrderShortMboMessage) -- 101
  | orderBookClearMessage (message : OrderBookClearMessage) -- 121
  | tradeMessage (message : TradeMessage) -- 80
  | instrumentDirectoryEquitiesMessage (message : InstrumentDirectoryEquitiesMessage) -- 82
  | statisticsSnapshotMessage (message : StatisticsSnapshotMessage) -- 107
  deriving DecidableEq, Repr

namespace Payload

/-- The Message Type each message is sent under -/
def tag : Payload → BitVec 8
  | .loginRequestMessage _ => 1
  | .recoveryRequestMessage _ => 129
  | .loginResponseMessage _ => 2
  | .recoveryResponseMessage _ => 130
  | .replayAndRecoveryCompleteMessage _ => 131
  | .systemEventMessage _ => 83
  | .instrumentStatusMessage _ => 72
  | .addOrderMboMessage _ => 65
  | .addOrderShortMboMessage _ => 101
  | .orderBookClearMessage _ => 121
  | .tradeMessage _ => 80
  | .instrumentDirectoryEquitiesMessage _ => 82
  | .statisticsSnapshotMessage _ => 107

def encode : Payload → List UInt8
  | .loginRequestMessage message => LoginRequestMessage.encode message
  | .recoveryRequestMessage message => RecoveryRequestMessage.encode message
  | .loginResponseMessage message => LoginResponseMessage.encode message
  | .recoveryResponseMessage message => RecoveryResponseMessage.encode message
  | .replayAndRecoveryCompleteMessage message => ReplayAndRecoveryCompleteMessage.encode message
  | .systemEventMessage message => SystemEventMessage.encode message
  | .instrumentStatusMessage message => InstrumentStatusMessage.encode message
  | .addOrderMboMessage message => AddOrderMboMessage.encode message
  | .addOrderShortMboMessage message => AddOrderShortMboMessage.encode message
  | .orderBookClearMessage message => OrderBookClearMessage.encode message
  | .tradeMessage message => TradeMessage.encode message
  | .instrumentDirectoryEquitiesMessage message => InstrumentDirectoryEquitiesMessage.encode message
  | .statisticsSnapshotMessage message => StatisticsSnapshotMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : Payload) : (encode message).length ≤ 310 := by
  cases message with
  | loginRequestMessage inner =>
    simp only [encode, LoginRequestMessage.encode_length]
    omega
  | recoveryRequestMessage inner =>
    simp only [encode, RecoveryRequestMessage.encode_length]
    omega
  | loginResponseMessage inner =>
    simp only [encode, LoginResponseMessage.encode_length]
    omega
  | recoveryResponseMessage inner =>
    simp only [encode, RecoveryResponseMessage.encode_length]
    omega
  | replayAndRecoveryCompleteMessage inner =>
    simp only [encode, ReplayAndRecoveryCompleteMessage.encode_length]
    omega
  | systemEventMessage inner =>
    simp only [encode, SystemEventMessage.encode_length]
    omega
  | instrumentStatusMessage inner =>
    simp only [encode, InstrumentStatusMessage.encode_length]
    omega
  | addOrderMboMessage inner =>
    simp only [encode, AddOrderMboMessage.encode_length]
    omega
  | addOrderShortMboMessage inner =>
    simp only [encode, AddOrderShortMboMessage.encode_length]
    omega
  | orderBookClearMessage inner =>
    simp only [encode, OrderBookClearMessage.encode_length]
    omega
  | tradeMessage inner =>
    simp only [encode, TradeMessage.encode_length]
    omega
  | instrumentDirectoryEquitiesMessage inner =>
    simp only [encode, InstrumentDirectoryEquitiesMessage.encode_length]
    omega
  | statisticsSnapshotMessage inner =>
    simp only [encode, StatisticsSnapshotMessage.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (Payload × List UInt8) :=
  if tag = 1 then (LoginRequestMessage.decode bytes).map fun (message, rest) => (.loginRequestMessage message, rest)
  else if tag = 129 then (RecoveryRequestMessage.decode bytes).map fun (message, rest) => (.recoveryRequestMessage message, rest)
  else if tag = 2 then (LoginResponseMessage.decode bytes).map fun (message, rest) => (.loginResponseMessage message, rest)
  else if tag = 130 then (RecoveryResponseMessage.decode bytes).map fun (message, rest) => (.recoveryResponseMessage message, rest)
  else if tag = 131 then (ReplayAndRecoveryCompleteMessage.decode bytes).map fun (message, rest) => (.replayAndRecoveryCompleteMessage message, rest)
  else if tag = 83 then (SystemEventMessage.decode bytes).map fun (message, rest) => (.systemEventMessage message, rest)
  else if tag = 72 then (InstrumentStatusMessage.decode bytes).map fun (message, rest) => (.instrumentStatusMessage message, rest)
  else if tag = 65 then (AddOrderMboMessage.decode bytes).map fun (message, rest) => (.addOrderMboMessage message, rest)
  else if tag = 101 then (AddOrderShortMboMessage.decode bytes).map fun (message, rest) => (.addOrderShortMboMessage message, rest)
  else if tag = 121 then (OrderBookClearMessage.decode bytes).map fun (message, rest) => (.orderBookClearMessage message, rest)
  else if tag = 80 then (TradeMessage.decode bytes).map fun (message, rest) => (.tradeMessage message, rest)
  else if tag = 82 then (InstrumentDirectoryEquitiesMessage.decode bytes).map fun (message, rest) => (.instrumentDirectoryEquitiesMessage message, rest)
  else if tag = 107 then (StatisticsSnapshotMessage.decode bytes).map fun (message, rest) => (.statisticsSnapshotMessage message, rest)
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
  | recoveryRequestMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, RecoveryRequestMessage.encode_length]
    omega
  | loginResponseMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, LoginResponseMessage.encode_length]
    omega
  | recoveryResponseMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, RecoveryResponseMessage.encode_length]
    omega
  | replayAndRecoveryCompleteMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, ReplayAndRecoveryCompleteMessage.encode_length]
    omega
  | systemEventMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, SystemEventMessage.encode_length]
    omega
  | instrumentStatusMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, InstrumentStatusMessage.encode_length]
    omega
  | addOrderMboMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, AddOrderMboMessage.encode_length]
    omega
  | addOrderShortMboMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, AddOrderShortMboMessage.encode_length]
    omega
  | orderBookClearMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, OrderBookClearMessage.encode_length]
    omega
  | tradeMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, TradeMessage.encode_length]
    omega
  | instrumentDirectoryEquitiesMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, InstrumentDirectoryEquitiesMessage.encode_length]
    omega
  | statisticsSnapshotMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, StatisticsSnapshotMessage.encode_length]
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

end Omi.LsegLseLevel2mborecoveryGtpV262
