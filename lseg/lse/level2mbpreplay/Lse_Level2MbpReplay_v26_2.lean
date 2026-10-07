import Wire

/-!
# London Stock Exchange Level 2 MBP Replay v26.2

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Note: Allowed Book Types is a bit field set, proven as its 1 byte integer rather than bit by bit.

Note: Trade Flags is a bit field set, proven as its 1 byte integer rather than bit by bit.

Note: Tcp Unit's Length is written from its body but not checked on decode, since the body has no bound the prefix must fit; the body is read by its content.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.LsegLseLevel2mbpreplayGtpV262

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

/-- Auction Info: one byte code -/
def AuctionInfo.codes : List UInt8 :=
  [0x30, 0x42, 0x4E, 0x4F, 0x53]

inductive AuctionInfo where
  | notApplicable -- Not Applicable
  | buyImbalance -- Buy Imbalance
  | noImbalance -- No Imbalance
  | insufficientOrdersForAuction -- Insufficient Orders For Auction
  | sellImbalance -- Sell Imbalance
  | unlisted (byte : { byte : UInt8 // byte ∉ AuctionInfo.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace AuctionInfo

def toByte : AuctionInfo → UInt8
  | .notApplicable => 0x30
  | .buyImbalance => 0x42
  | .noImbalance => 0x4E
  | .insufficientOrdersForAuction => 0x4F
  | .sellImbalance => 0x53
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : AuctionInfo :=
  if byte = 0x30 then .notApplicable
  else if byte = 0x42 then .buyImbalance
  else if byte = 0x4E then .noImbalance
  else if byte = 0x4F then .insufficientOrdersForAuction
  else .sellImbalance

def ofByte (byte : UInt8) : AuctionInfo :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : AuctionInfo) : ofByte value.toByte = value := by
  cases value with
  | notApplicable => decide
  | buyImbalance => decide
  | noImbalance => decide
  | insufficientOrdersForAuction => decide
  | sellImbalance => decide
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

/-- Opening Closing Price Indicator: one byte code -/
def OpeningClosingPriceIndicator.codes : List UInt8 :=
  [0x41, 0x42, 0x43, 0x44, 0x45, 0x46, 0x49]

inductive OpeningClosingPriceIndicator where
  | ut -- Ut
  | at_ -- At
  | midOfBbo -- Mid Of Bbo
  | lastAt -- Last At
  | lastUt -- Last Ut
  | manual -- Manual
  | previousClose -- Previous Close
  | unlisted (byte : { byte : UInt8 // byte ∉ OpeningClosingPriceIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OpeningClosingPriceIndicator

def toByte : OpeningClosingPriceIndicator → UInt8
  | .ut => 0x41
  | .at_ => 0x42
  | .midOfBbo => 0x43
  | .lastAt => 0x44
  | .lastUt => 0x45
  | .manual => 0x46
  | .previousClose => 0x49
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OpeningClosingPriceIndicator :=
  if byte = 0x41 then .ut
  else if byte = 0x42 then .at_
  else if byte = 0x43 then .midOfBbo
  else if byte = 0x44 then .lastAt
  else if byte = 0x45 then .lastUt
  else if byte = 0x46 then .manual
  else .previousClose

def ofByte (byte : UInt8) : OpeningClosingPriceIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OpeningClosingPriceIndicator) : ofByte value.toByte = value := by
  cases value with
  | ut => decide
  | at_ => decide
  | midOfBbo => decide
  | lastAt => decide
  | lastUt => decide
  | manual => decide
  | previousClose => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : OpeningClosingPriceIndicator) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (OpeningClosingPriceIndicator × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : OpeningClosingPriceIndicator) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : OpeningClosingPriceIndicator) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end OpeningClosingPriceIndicator

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
  reserved8 : Alpha 8
  dynamicCircuitBreakerTolerances : BitVec 64
  staticCircuitBreakerTolerances : BitVec 64
  segment : Alpha 6
  reserved12 : Alpha 12
  reserved11 : Alpha 11
  currency : Alpha 3
  partitionId : Alpha 1
  reserved4 : Alpha 4
  averageDailyTurnoverAdt : BitVec 64
  secondReserved8 : Alpha 8
  reserved1 : Alpha 1
  thirdReserved8 : Alpha 8
  fourthReserved8 : Alpha 8
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
    ++ (Alpha.encode message.reserved8
    ++ (encodeUIntLE 8 message.dynamicCircuitBreakerTolerances
    ++ (encodeUIntLE 8 message.staticCircuitBreakerTolerances
    ++ (Alpha.encode message.segment
    ++ (Alpha.encode message.reserved12
    ++ (Alpha.encode message.reserved11
    ++ (Alpha.encode message.currency
    ++ (Alpha.encode message.partitionId
    ++ (Alpha.encode message.reserved4
    ++ (encodeUIntLE 8 message.averageDailyTurnoverAdt
    ++ (Alpha.encode message.secondReserved8
    ++ (Alpha.encode message.reserved1
    ++ (Alpha.encode message.thirdReserved8
    ++ (Alpha.encode message.fourthReserved8))))))))))))))))))))

def decode (bytes : List UInt8) : Option (InstrumentDirectoryMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  let (instrument, bytes) ← decodeUIntLE 8 bytes
  let (isin, bytes) ← Alpha.decode 12 bytes
  let (allowedBookTypes, bytes) ← decodeUIntLE 1 bytes
  let (sourceVenue, bytes) ← decodeUIntLE 2 bytes
  let (venueInstrumentId, bytes) ← Alpha.decode 11 bytes
  let (tickId, bytes) ← Alpha.decode 2 bytes
  let (reserved8, bytes) ← Alpha.decode 8 bytes
  let (dynamicCircuitBreakerTolerances, bytes) ← decodeUIntLE 8 bytes
  let (staticCircuitBreakerTolerances, bytes) ← decodeUIntLE 8 bytes
  let (segment, bytes) ← Alpha.decode 6 bytes
  let (reserved12, bytes) ← Alpha.decode 12 bytes
  let (reserved11, bytes) ← Alpha.decode 11 bytes
  let (currency, bytes) ← Alpha.decode 3 bytes
  let (partitionId, bytes) ← Alpha.decode 1 bytes
  let (reserved4, bytes) ← Alpha.decode 4 bytes
  let (averageDailyTurnoverAdt, bytes) ← decodeUIntLE 8 bytes
  let (secondReserved8, bytes) ← Alpha.decode 8 bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  let (thirdReserved8, bytes) ← Alpha.decode 8 bytes
  let (fourthReserved8, bytes) ← Alpha.decode 8 bytes
  pure ({ timestamp, instrument, isin, allowedBookTypes, sourceVenue, venueInstrumentId, tickId, reserved8, dynamicCircuitBreakerTolerances, staticCircuitBreakerTolerances, segment, reserved12, reserved11, currency, partitionId, reserved4, averageDailyTurnoverAdt, secondReserved8, reserved1, thirdReserved8, fourthReserved8 }, bytes)

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

/-- Add Order Mbp Message: 47 bytes -/
structure AddOrderMbpMessage where
  timestamp : BitVec 64
  side : Side
  size : BitVec 64
  instrument : BitVec 64
  price : BitVec 64
  reserved8 : Alpha 8
  sourceVenue : BitVec 16
  orderBookType : BitVec 8
  splits : BitVec 16
  depth : BitVec 8
  deriving DecidableEq, Repr

namespace AddOrderMbpMessage

def encode (message : AddOrderMbpMessage) : List UInt8 :=
  encodeUIntLE 8 message.timestamp
    ++ (Side.encode message.side
    ++ (encodeUIntLE 8 message.size
    ++ (encodeUIntLE 8 message.instrument
    ++ (encodeUIntLE 8 message.price
    ++ (Alpha.encode message.reserved8
    ++ (encodeUIntLE 2 message.sourceVenue
    ++ (encodeUIntLE 1 message.orderBookType
    ++ (encodeUIntLE 2 message.splits
    ++ (encodeUIntLE 1 message.depth)))))))))

def decode (bytes : List UInt8) : Option (AddOrderMbpMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  let (side, bytes) ← Side.decode bytes
  let (size, bytes) ← decodeUIntLE 8 bytes
  let (instrument, bytes) ← decodeUIntLE 8 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (reserved8, bytes) ← Alpha.decode 8 bytes
  let (sourceVenue, bytes) ← decodeUIntLE 2 bytes
  let (orderBookType, bytes) ← decodeUIntLE 1 bytes
  let (splits, bytes) ← decodeUIntLE 2 bytes
  let (depth, bytes) ← decodeUIntLE 1 bytes
  pure ({ timestamp, side, size, instrument, price, reserved8, sourceVenue, orderBookType, splits, depth }, bytes)

@[simp] theorem encode_length (message : AddOrderMbpMessage) : (encode message).length = 47 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Side.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : AddOrderMbpMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : AddOrderMbpMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end AddOrderMbpMessage

/-- Add Order Short Mbp Message: 26 bytes -/
structure AddOrderShortMbpMessage where
  size : BitVec 64
  price : BitVec 64
  reserved8 : Alpha 8
  splits : BitVec 16
  deriving DecidableEq, Repr

namespace AddOrderShortMbpMessage

def encode (message : AddOrderShortMbpMessage) : List UInt8 :=
  encodeUIntLE 8 message.size
    ++ (encodeUIntLE 8 message.price
    ++ (Alpha.encode message.reserved8
    ++ (encodeUIntLE 2 message.splits)))

def decode (bytes : List UInt8) : Option (AddOrderShortMbpMessage × List UInt8) := do
  let (size, bytes) ← decodeUIntLE 8 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (reserved8, bytes) ← Alpha.decode 8 bytes
  let (splits, bytes) ← decodeUIntLE 2 bytes
  pure ({ size, price, reserved8, splits }, bytes)

@[simp] theorem encode_length (message : AddOrderShortMbpMessage) : (encode message).length = 26 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : AddOrderShortMbpMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : AddOrderShortMbpMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end AddOrderShortMbpMessage

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
  openingClosingPriceIndicator : OpeningClosingPriceIndicator
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
    ++ (OpeningClosingPriceIndicator.encode message.openingClosingPriceIndicator)))))))))

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
  let (openingClosingPriceIndicator, bytes) ← OpeningClosingPriceIndicator.decode bytes
  pure ({ timestamp, instrument, sourceVenue, statisticType, statisticPrice, statisticSize, auctionType, imbalanceQuantity, auctionInfo, openingClosingPriceIndicator }, bytes)

@[simp] theorem encode_length (message : StatisticsUpdateMessage) : (encode message).length = 47 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, AuctionType.encode_length, AuctionInfo.encode_length, OpeningClosingPriceIndicator.encode_length]

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
  rw [OpeningClosingPriceIndicator.decode_encode, some_bind]
  rfl

end StatisticsUpdateMessage

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
  | addOrderMbpMessage (message : AddOrderMbpMessage) -- 102
  | addOrderShortMbpMessage (message : AddOrderShortMbpMessage) -- 103
  | orderBookClearMessage (message : OrderBookClearMessage) -- 121
  | tradeMessage (message : TradeMessage) -- 80
  | statisticsMessage (message : StatisticsMessage) -- 119
  | statisticsUpdateMessage (message : StatisticsUpdateMessage) -- 106
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
  | .addOrderMbpMessage _ => 102
  | .addOrderShortMbpMessage _ => 103
  | .orderBookClearMessage _ => 121
  | .tradeMessage _ => 80
  | .statisticsMessage _ => 119
  | .statisticsUpdateMessage _ => 106

def encode : Payload → List UInt8
  | .loginRequestMessage message => LoginRequestMessage.encode message
  | .replayRequestMessage message => ReplayRequestMessage.encode message
  | .loginResponseMessage message => LoginResponseMessage.encode message
  | .replayResponseMessage message => ReplayResponseMessage.encode message
  | .replayAndRecoveryCompleteMessage message => ReplayAndRecoveryCompleteMessage.encode message
  | .systemEventMessage message => SystemEventMessage.encode message
  | .instrumentDirectoryMessage message => InstrumentDirectoryMessage.encode message
  | .instrumentStatusMessage message => InstrumentStatusMessage.encode message
  | .addOrderMbpMessage message => AddOrderMbpMessage.encode message
  | .addOrderShortMbpMessage message => AddOrderShortMbpMessage.encode message
  | .orderBookClearMessage message => OrderBookClearMessage.encode message
  | .tradeMessage message => TradeMessage.encode message
  | .statisticsMessage message => StatisticsMessage.encode message
  | .statisticsUpdateMessage message => StatisticsUpdateMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : Payload) : (encode message).length ≤ 138 := by
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
  | addOrderMbpMessage inner =>
    simp only [encode, AddOrderMbpMessage.encode_length]
    omega
  | addOrderShortMbpMessage inner =>
    simp only [encode, AddOrderShortMbpMessage.encode_length]
    omega
  | orderBookClearMessage inner =>
    simp only [encode, OrderBookClearMessage.encode_length]
    omega
  | tradeMessage inner =>
    simp only [encode, TradeMessage.encode_length]
    omega
  | statisticsMessage inner =>
    simp only [encode, StatisticsMessage.encode_length]
    omega
  | statisticsUpdateMessage inner =>
    simp only [encode, StatisticsUpdateMessage.encode_length]
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
  else if tag = 102 then (AddOrderMbpMessage.decode bytes).map fun (message, rest) => (.addOrderMbpMessage message, rest)
  else if tag = 103 then (AddOrderShortMbpMessage.decode bytes).map fun (message, rest) => (.addOrderShortMbpMessage message, rest)
  else if tag = 121 then (OrderBookClearMessage.decode bytes).map fun (message, rest) => (.orderBookClearMessage message, rest)
  else if tag = 80 then (TradeMessage.decode bytes).map fun (message, rest) => (.tradeMessage message, rest)
  else if tag = 119 then (StatisticsMessage.decode bytes).map fun (message, rest) => (.statisticsMessage message, rest)
  else if tag = 106 then (StatisticsUpdateMessage.decode bytes).map fun (message, rest) => (.statisticsUpdateMessage message, rest)
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
  | addOrderMbpMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, AddOrderMbpMessage.encode_length]
    omega
  | addOrderShortMbpMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, AddOrderShortMbpMessage.encode_length]
    omega
  | orderBookClearMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, OrderBookClearMessage.encode_length]
    omega
  | tradeMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, TradeMessage.encode_length]
    omega
  | statisticsMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, StatisticsMessage.encode_length]
    omega
  | statisticsUpdateMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, StatisticsUpdateMessage.encode_length]
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

end Omi.LsegLseLevel2mbpreplayGtpV262
