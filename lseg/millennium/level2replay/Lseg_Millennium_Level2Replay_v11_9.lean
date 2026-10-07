import Wire

/-!
# London Stock Exchange  v11.9

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Note: Symbol Status Flags is a bit field set, proven as its 1 byte integer rather than bit by bit.

Note: Add Order Flags is a bit field set, proven as its 1 byte integer rather than bit by bit.

Note: Add Attributed Order Flags is a bit field set, proven as its 1 byte integer rather than bit by bit.

Note: Order Deleted Flags is a bit field set, proven as its 1 byte integer rather than bit by bit.

Note: Order Modified Flags is a bit field set, proven as its 1 byte integer rather than bit by bit.

Note: Order Book Clear Flags is a bit field set, proven as its 1 byte integer rather than bit by bit.

Note: Pt Mod Flags is a bit field set, proven as its 1 byte integer rather than bit by bit.

Note: Statistics Reserved is a bit field set, proven as its 1 byte integer rather than bit by bit.

Note: Tcp Unit's Length is written from its body but not checked on decode, since the body has no bound the prefix must fit; the body is read by its content.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.LsegMillenniumLevel2replayMitchV119

/-- Login Status: one byte code -/
def LoginStatus.codes : List UInt8 :=
  [0x41, 0x61, 0x62, 0x63, 0x64, 0x65]

inductive LoginStatus where
  | loginAccepted -- Login Accepted
  | compIdInactiveLocked -- Comp Id Inactive Locked
  | loginLimitReached -- Login Limit Reached
  | serviceUnavailable -- Service Unavailable
  | concurrentLimitReached -- Concurrent Limit Reached
  | failedOther -- Failed Other
  | unlisted (byte : { byte : UInt8 // byte ∉ LoginStatus.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace LoginStatus

def toByte : LoginStatus → UInt8
  | .loginAccepted => 0x41
  | .compIdInactiveLocked => 0x61
  | .loginLimitReached => 0x62
  | .serviceUnavailable => 0x63
  | .concurrentLimitReached => 0x64
  | .failedOther => 0x65
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : LoginStatus :=
  if byte = 0x41 then .loginAccepted
  else if byte = 0x61 then .compIdInactiveLocked
  else if byte = 0x62 then .loginLimitReached
  else if byte = 0x63 then .serviceUnavailable
  else if byte = 0x64 then .concurrentLimitReached
  else .failedOther

def ofByte (byte : UInt8) : LoginStatus :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : LoginStatus) : ofByte value.toByte = value := by
  cases value with
  | loginAccepted => decide
  | compIdInactiveLocked => decide
  | loginLimitReached => decide
  | serviceUnavailable => decide
  | concurrentLimitReached => decide
  | failedOther => decide
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
  [0x41, 0x44, 0x49, 0x4F, 0x55, 0x64, 0x65, 0x63]

inductive ReplayStatus where
  | requestAccepted -- Request Accepted
  | requestLimitReached -- Request Limit Reached
  | invalidMarketDataGroup -- Invalid Market Data Group
  | outOfRange -- Out Of Range
  | replayUnavailable -- Replay Unavailable
  | unsupportedMessageType -- Unsupported Message Type
  | failedOther -- Failed Other
  | concurrentLimitReached -- Concurrent Limit Reached
  | unlisted (byte : { byte : UInt8 // byte ∉ ReplayStatus.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ReplayStatus

def toByte : ReplayStatus → UInt8
  | .requestAccepted => 0x41
  | .requestLimitReached => 0x44
  | .invalidMarketDataGroup => 0x49
  | .outOfRange => 0x4F
  | .replayUnavailable => 0x55
  | .unsupportedMessageType => 0x64
  | .failedOther => 0x65
  | .concurrentLimitReached => 0x63
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ReplayStatus :=
  if byte = 0x41 then .requestAccepted
  else if byte = 0x44 then .requestLimitReached
  else if byte = 0x49 then .invalidMarketDataGroup
  else if byte = 0x4F then .outOfRange
  else if byte = 0x55 then .replayUnavailable
  else if byte = 0x64 then .unsupportedMessageType
  else if byte = 0x65 then .failedOther
  else .concurrentLimitReached

def ofByte (byte : UInt8) : ReplayStatus :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ReplayStatus) : ofByte value.toByte = value := by
  cases value with
  | requestAccepted => decide
  | requestLimitReached => decide
  | invalidMarketDataGroup => decide
  | outOfRange => decide
  | replayUnavailable => decide
  | unsupportedMessageType => decide
  | failedOther => decide
  | concurrentLimitReached => decide
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

/-- Symbol Status: one byte code -/
def SymbolStatus.codes : List UInt8 :=
  [0x20, 0x53, 0x61, 0x48]

inductive SymbolStatus where
  | active -- Active
  | suspended -- Suspended
  | inactive -- Inactive
  | halt -- Halt
  | unlisted (byte : { byte : UInt8 // byte ∉ SymbolStatus.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace SymbolStatus

def toByte : SymbolStatus → UInt8
  | .active => 0x20
  | .suspended => 0x53
  | .inactive => 0x61
  | .halt => 0x48
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : SymbolStatus :=
  if byte = 0x20 then .active
  else if byte = 0x53 then .suspended
  else if byte = 0x61 then .inactive
  else .halt

def ofByte (byte : UInt8) : SymbolStatus :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : SymbolStatus) : ofByte value.toByte = value := by
  cases value with
  | active => decide
  | suspended => decide
  | inactive => decide
  | halt => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : SymbolStatus) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (SymbolStatus × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : SymbolStatus) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : SymbolStatus) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end SymbolStatus

/-- Trading Status: one byte code -/
def TradingStatus.codes : List UInt8 :=
  [0x20, 0x48, 0x54, 0x61, 0x62, 0x63, 0x64, 0x65, 0x66, 0x6C, 0x6D, 0x6E, 0x6F, 0x71, 0x72, 0x74, 0x77, 0x78, 0x75, 0x47]

inductive TradingStatus where
  | active -- Active
  | halt -- Halt
  | regularTradingStartOfTradeReporting -- Regular Trading Start Of Trade Reporting
  | openingFirstAuctionCall -- Opening First Auction Call
  | postClose -- Post Close
  | marketCloseSystemShutdown -- Market Close System Shutdown
  | closingAuctionCall -- Closing Auction Call
  | aespAuctionCall -- Aesp Auction Call
  | resumeAuctionCall -- Resume Auction Call
  | pause -- Pause
  | preMandatory -- Pre Mandatory
  | mandatory -- Mandatory
  | postMandatory -- Post Mandatory
  | edspAuctionCall -- Edsp Auction Call
  | periodicAuctionCall -- Periodic Auction Call
  | endTradeReporting -- End Trade Reporting
  | noActiveSession -- No Active Session
  | endOfPostClose -- End Of Post Close
  | closingPriceCrossing -- Closing Price Crossing
  | scheduledLevel1OnlyAuction -- Scheduled Level 1 Only Auction
  | unlisted (byte : { byte : UInt8 // byte ∉ TradingStatus.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TradingStatus

def toByte : TradingStatus → UInt8
  | .active => 0x20
  | .halt => 0x48
  | .regularTradingStartOfTradeReporting => 0x54
  | .openingFirstAuctionCall => 0x61
  | .postClose => 0x62
  | .marketCloseSystemShutdown => 0x63
  | .closingAuctionCall => 0x64
  | .aespAuctionCall => 0x65
  | .resumeAuctionCall => 0x66
  | .pause => 0x6C
  | .preMandatory => 0x6D
  | .mandatory => 0x6E
  | .postMandatory => 0x6F
  | .edspAuctionCall => 0x71
  | .periodicAuctionCall => 0x72
  | .endTradeReporting => 0x74
  | .noActiveSession => 0x77
  | .endOfPostClose => 0x78
  | .closingPriceCrossing => 0x75
  | .scheduledLevel1OnlyAuction => 0x47
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TradingStatus :=
  if byte = 0x20 then .active
  else if byte = 0x48 then .halt
  else if byte = 0x54 then .regularTradingStartOfTradeReporting
  else if byte = 0x61 then .openingFirstAuctionCall
  else if byte = 0x62 then .postClose
  else if byte = 0x63 then .marketCloseSystemShutdown
  else if byte = 0x64 then .closingAuctionCall
  else if byte = 0x65 then .aespAuctionCall
  else if byte = 0x66 then .resumeAuctionCall
  else if byte = 0x6C then .pause
  else if byte = 0x6D then .preMandatory
  else if byte = 0x6E then .mandatory
  else if byte = 0x6F then .postMandatory
  else if byte = 0x71 then .edspAuctionCall
  else if byte = 0x72 then .periodicAuctionCall
  else if byte = 0x74 then .endTradeReporting
  else if byte = 0x77 then .noActiveSession
  else if byte = 0x78 then .endOfPostClose
  else if byte = 0x75 then .closingPriceCrossing
  else .scheduledLevel1OnlyAuction

def ofByte (byte : UInt8) : TradingStatus :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TradingStatus) : ofByte value.toByte = value := by
  cases value with
  | active => decide
  | halt => decide
  | regularTradingStartOfTradeReporting => decide
  | openingFirstAuctionCall => decide
  | postClose => decide
  | marketCloseSystemShutdown => decide
  | closingAuctionCall => decide
  | aespAuctionCall => decide
  | resumeAuctionCall => decide
  | pause => decide
  | preMandatory => decide
  | mandatory => decide
  | postMandatory => decide
  | edspAuctionCall => decide
  | periodicAuctionCall => decide
  | endTradeReporting => decide
  | noActiveSession => decide
  | endOfPostClose => decide
  | closingPriceCrossing => decide
  | scheduledLevel1OnlyAuction => decide
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

/-- Printable: one byte code -/
def Printable.codes : List UInt8 :=
  [0x4E, 0x59]

inductive Printable where
  | nonPrintable -- Non Printable
  | printable -- Printable
  | unlisted (byte : { byte : UInt8 // byte ∉ Printable.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Printable

def toByte : Printable → UInt8
  | .nonPrintable => 0x4E
  | .printable => 0x59
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Printable :=
  if byte = 0x4E then .nonPrintable
  else .printable

def ofByte (byte : UInt8) : Printable :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Printable) : ofByte value.toByte = value := by
  cases value with
  | nonPrintable => decide
  | printable => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Printable) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Printable × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Printable) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : Printable) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Printable

/-- Auction Type: one byte code -/
def AuctionType.codes : List UInt8 :=
  [0x43, 0x4F, 0x41, 0x42, 0x45, 0x46, 0x47]

inductive AuctionType where
  | closingAuction -- Closing Auction
  | openingAuction -- Opening Auction
  | aesp -- Aesp
  | edsp -- Edsp
  | resumeAuction -- Resume Auction
  | periodicAuction -- Periodic Auction
  | scheduledLevel1OnlyAuction -- Scheduled Level 1 Only Auction
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
  | .scheduledLevel1OnlyAuction => 0x47
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : AuctionType :=
  if byte = 0x43 then .closingAuction
  else if byte = 0x4F then .openingAuction
  else if byte = 0x41 then .aesp
  else if byte = 0x42 then .edsp
  else if byte = 0x45 then .resumeAuction
  else if byte = 0x46 then .periodicAuction
  else .scheduledLevel1OnlyAuction

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
  | scheduledLevel1OnlyAuction => decide
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

/-- Statistic Type: one byte code -/
def StatisticType.codes : List UInt8 :=
  [0x4F, 0x43]

inductive StatisticType where
  | openingPrice -- Opening Price
  | closingPrice -- Closing Price
  | unlisted (byte : { byte : UInt8 // byte ∉ StatisticType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace StatisticType

def toByte : StatisticType → UInt8
  | .openingPrice => 0x4F
  | .closingPrice => 0x43
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : StatisticType :=
  if byte = 0x4F then .openingPrice
  else .closingPrice

def ofByte (byte : UInt8) : StatisticType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : StatisticType) : ofByte value.toByte = value := by
  cases value with
  | openingPrice => decide
  | closingPrice => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : StatisticType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (StatisticType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : StatisticType) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : StatisticType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end StatisticType

/-- Open Close Price Indicator: one byte code -/
def OpenClosePriceIndicator.codes : List UInt8 :=
  [0x41, 0x42, 0x43, 0x44, 0x45, 0x46, 0x49]

inductive OpenClosePriceIndicator where
  | ut -- Ut
  | at_ -- At
  | midOfBbo -- Mid Of Bbo
  | lastAt -- Last At
  | lastUt -- Last Ut
  | manual -- Manual
  | derivedFromPreviousClose -- Derived From Previous Close
  | unlisted (byte : { byte : UInt8 // byte ∉ OpenClosePriceIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OpenClosePriceIndicator

def toByte : OpenClosePriceIndicator → UInt8
  | .ut => 0x41
  | .at_ => 0x42
  | .midOfBbo => 0x43
  | .lastAt => 0x44
  | .lastUt => 0x45
  | .manual => 0x46
  | .derivedFromPreviousClose => 0x49
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OpenClosePriceIndicator :=
  if byte = 0x41 then .ut
  else if byte = 0x42 then .at_
  else if byte = 0x43 then .midOfBbo
  else if byte = 0x44 then .lastAt
  else if byte = 0x45 then .lastUt
  else if byte = 0x46 then .manual
  else .derivedFromPreviousClose

def ofByte (byte : UInt8) : OpenClosePriceIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OpenClosePriceIndicator) : ofByte value.toByte = value := by
  cases value with
  | ut => decide
  | at_ => decide
  | midOfBbo => decide
  | lastAt => decide
  | lastUt => decide
  | manual => decide
  | derivedFromPreviousClose => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : OpenClosePriceIndicator) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (OpenClosePriceIndicator × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : OpenClosePriceIndicator) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : OpenClosePriceIndicator) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end OpenClosePriceIndicator

/-- Login Request Message: 16 bytes -/
structure LoginRequestMessage where
  username : Alpha 6
  password : Alpha 10
  deriving DecidableEq, Repr

namespace LoginRequestMessage

def encode (message : LoginRequestMessage) : List UInt8 :=
  Alpha.encode message.username
    ++ (Alpha.encode message.password)

def decode (bytes : List UInt8) : Option (LoginRequestMessage × List UInt8) := do
  let (username, bytes) ← Alpha.decode 6 bytes
  let (password, bytes) ← Alpha.decode 10 bytes
  pure ({ username, password }, bytes)

@[simp] theorem encode_length (message : LoginRequestMessage) : (encode message).length = 16 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : LoginRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LoginRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end LoginRequestMessage

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

/-- Replay Request Message: 7 bytes -/
structure ReplayRequestMessage where
  marketDataGroup : Alpha 1
  firstMessage : BitVec 32
  count : BitVec 16
  deriving DecidableEq, Repr

namespace ReplayRequestMessage

def encode (message : ReplayRequestMessage) : List UInt8 :=
  Alpha.encode message.marketDataGroup
    ++ (encodeUIntLE 4 message.firstMessage
    ++ (encodeUIntLE 2 message.count))

def decode (bytes : List UInt8) : Option (ReplayRequestMessage × List UInt8) := do
  let (marketDataGroup, bytes) ← Alpha.decode 1 bytes
  let (firstMessage, bytes) ← decodeUIntLE 4 bytes
  let (count, bytes) ← decodeUIntLE 2 bytes
  pure ({ marketDataGroup, firstMessage, count }, bytes)

@[simp] theorem encode_length (message : ReplayRequestMessage) : (encode message).length = 7 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : ReplayRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ReplayRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end ReplayRequestMessage

/-- Replay Response Message: 8 bytes -/
structure ReplayResponseMessage where
  marketDataGroup : Alpha 1
  firstMessage : BitVec 32
  count : BitVec 16
  replayStatus : ReplayStatus
  deriving DecidableEq, Repr

namespace ReplayResponseMessage

def encode (message : ReplayResponseMessage) : List UInt8 :=
  Alpha.encode message.marketDataGroup
    ++ (encodeUIntLE 4 message.firstMessage
    ++ (encodeUIntLE 2 message.count
    ++ (ReplayStatus.encode message.replayStatus)))

def decode (bytes : List UInt8) : Option (ReplayResponseMessage × List UInt8) := do
  let (marketDataGroup, bytes) ← Alpha.decode 1 bytes
  let (firstMessage, bytes) ← decodeUIntLE 4 bytes
  let (count, bytes) ← decodeUIntLE 2 bytes
  let (replayStatus, bytes) ← ReplayStatus.decode bytes
  pure ({ marketDataGroup, firstMessage, count, replayStatus }, bytes)

@[simp] theorem encode_length (message : ReplayResponseMessage) : (encode message).length = 8 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUIntLE_length, ReplayStatus.encode_length]

theorem encode_length_pos (message : ReplayResponseMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ReplayResponseMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [ReplayStatus.decode_encode, some_bind]
  rfl

end ReplayResponseMessage

/-- Time Message: 4 bytes -/
structure TimeMessage where
  seconds : BitVec 32
  deriving DecidableEq, Repr

namespace TimeMessage

def encode (message : TimeMessage) : List UInt8 :=
  encodeUIntLE 4 message.seconds

def decode (bytes : List UInt8) : Option (TimeMessage × List UInt8) := do
  let (seconds, bytes) ← decodeUIntLE 4 bytes
  pure ({ seconds }, bytes)

@[simp] theorem encode_length (message : TimeMessage) : (encode message).length = 4 := by
  unfold encode
  simp only [encodeUIntLE_length]

theorem encode_length_pos (message : TimeMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TimeMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end TimeMessage

/-- System Event Message: 5 bytes -/
structure SystemEventMessage where
  nanosecond : BitVec 32
  eventCode : EventCode
  deriving DecidableEq, Repr

namespace SystemEventMessage

def encode (message : SystemEventMessage) : List UInt8 :=
  encodeUIntLE 4 message.nanosecond
    ++ (EventCode.encode message.eventCode)

def decode (bytes : List UInt8) : Option (SystemEventMessage × List UInt8) := do
  let (nanosecond, bytes) ← decodeUIntLE 4 bytes
  let (eventCode, bytes) ← EventCode.decode bytes
  pure ({ nanosecond, eventCode }, bytes)

@[simp] theorem encode_length (message : SystemEventMessage) : (encode message).length = 5 := by
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
  rw [EventCode.decode_encode, some_bind]
  rfl

end SystemEventMessage

/-- Symbol Directory Message: 63 bytes -/
structure SymbolDirectoryMessage where
  nanosecond : BitVec 32
  instrumentId : BitVec 32
  reservedA : Alpha 1
  reservedB : Alpha 1
  symbolStatus : SymbolStatus
  isin : Alpha 12
  sedol : Alpha 12
  segment : Alpha 6
  underlying : Alpha 6
  currency : Alpha 3
  reservedByte : Alpha 1
  reserved4 : Alpha 4
  previousClosePrice : BitVec 64
  deriving DecidableEq, Repr

namespace SymbolDirectoryMessage

def encode (message : SymbolDirectoryMessage) : List UInt8 :=
  encodeUIntLE 4 message.nanosecond
    ++ (encodeUIntLE 4 message.instrumentId
    ++ (Alpha.encode message.reservedA
    ++ (Alpha.encode message.reservedB
    ++ (SymbolStatus.encode message.symbolStatus
    ++ (Alpha.encode message.isin
    ++ (Alpha.encode message.sedol
    ++ (Alpha.encode message.segment
    ++ (Alpha.encode message.underlying
    ++ (Alpha.encode message.currency
    ++ (Alpha.encode message.reservedByte
    ++ (Alpha.encode message.reserved4
    ++ (encodeUIntLE 8 message.previousClosePrice))))))))))))

def decode (bytes : List UInt8) : Option (SymbolDirectoryMessage × List UInt8) := do
  let (nanosecond, bytes) ← decodeUIntLE 4 bytes
  let (instrumentId, bytes) ← decodeUIntLE 4 bytes
  let (reservedA, bytes) ← Alpha.decode 1 bytes
  let (reservedB, bytes) ← Alpha.decode 1 bytes
  let (symbolStatus, bytes) ← SymbolStatus.decode bytes
  let (isin, bytes) ← Alpha.decode 12 bytes
  let (sedol, bytes) ← Alpha.decode 12 bytes
  let (segment, bytes) ← Alpha.decode 6 bytes
  let (underlying, bytes) ← Alpha.decode 6 bytes
  let (currency, bytes) ← Alpha.decode 3 bytes
  let (reservedByte, bytes) ← Alpha.decode 1 bytes
  let (reserved4, bytes) ← Alpha.decode 4 bytes
  let (previousClosePrice, bytes) ← decodeUIntLE 8 bytes
  pure ({ nanosecond, instrumentId, reservedA, reservedB, symbolStatus, isin, sedol, segment, underlying, currency, reservedByte, reserved4, previousClosePrice }, bytes)

@[simp] theorem encode_length (message : SymbolDirectoryMessage) : (encode message).length = 63 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, SymbolStatus.encode_length]

theorem encode_length_pos (message : SymbolDirectoryMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SymbolDirectoryMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, SymbolStatus.decode_encode, some_bind]
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
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end SymbolDirectoryMessage

/-- Symbol Status Message: 26 bytes -/
structure SymbolStatusMessage where
  nanosecond : BitVec 32
  instrumentId : BitVec 32
  reservedA : Alpha 1
  reservedB : Alpha 1
  tradingStatus : TradingStatus
  symbolStatusFlags : BitVec 8
  reason : Alpha 4
  sessionChangeReason : BitVec 8
  newEndTime : Alpha 8
  bookType : BitVec 8
  deriving DecidableEq, Repr

namespace SymbolStatusMessage

def encode (message : SymbolStatusMessage) : List UInt8 :=
  encodeUIntLE 4 message.nanosecond
    ++ (encodeUIntLE 4 message.instrumentId
    ++ (Alpha.encode message.reservedA
    ++ (Alpha.encode message.reservedB
    ++ (TradingStatus.encode message.tradingStatus
    ++ (encodeUIntLE 1 message.symbolStatusFlags
    ++ (Alpha.encode message.reason
    ++ (encodeUIntLE 1 message.sessionChangeReason
    ++ (Alpha.encode message.newEndTime
    ++ (encodeUIntLE 1 message.bookType)))))))))

def decode (bytes : List UInt8) : Option (SymbolStatusMessage × List UInt8) := do
  let (nanosecond, bytes) ← decodeUIntLE 4 bytes
  let (instrumentId, bytes) ← decodeUIntLE 4 bytes
  let (reservedA, bytes) ← Alpha.decode 1 bytes
  let (reservedB, bytes) ← Alpha.decode 1 bytes
  let (tradingStatus, bytes) ← TradingStatus.decode bytes
  let (symbolStatusFlags, bytes) ← decodeUIntLE 1 bytes
  let (reason, bytes) ← Alpha.decode 4 bytes
  let (sessionChangeReason, bytes) ← decodeUIntLE 1 bytes
  let (newEndTime, bytes) ← Alpha.decode 8 bytes
  let (bookType, bytes) ← decodeUIntLE 1 bytes
  pure ({ nanosecond, instrumentId, reservedA, reservedB, tradingStatus, symbolStatusFlags, reason, sessionChangeReason, newEndTime, bookType }, bytes)

@[simp] theorem encode_length (message : SymbolStatusMessage) : (encode message).length = 26 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, TradingStatus.encode_length]

theorem encode_length_pos (message : SymbolStatusMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SymbolStatusMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, TradingStatus.decode_encode, some_bind]
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

end SymbolStatusMessage

/-- Add Order Message: 42 bytes -/
structure AddOrderMessage where
  nanosecond : BitVec 32
  orderId : BitVec 64
  side : Side
  quantity : BitVec 32
  instrumentId : BitVec 32
  reservedA : Alpha 1
  reservedB : Alpha 1
  price : BitVec 64
  addOrderFlags : BitVec 8
  reserved10 : Alpha 10
  deriving DecidableEq, Repr

namespace AddOrderMessage

def encode (message : AddOrderMessage) : List UInt8 :=
  encodeUIntLE 4 message.nanosecond
    ++ (encodeUIntLE 8 message.orderId
    ++ (Side.encode message.side
    ++ (encodeUIntLE 4 message.quantity
    ++ (encodeUIntLE 4 message.instrumentId
    ++ (Alpha.encode message.reservedA
    ++ (Alpha.encode message.reservedB
    ++ (encodeUIntLE 8 message.price
    ++ (encodeUIntLE 1 message.addOrderFlags
    ++ (Alpha.encode message.reserved10)))))))))

def decode (bytes : List UInt8) : Option (AddOrderMessage × List UInt8) := do
  let (nanosecond, bytes) ← decodeUIntLE 4 bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (side, bytes) ← Side.decode bytes
  let (quantity, bytes) ← decodeUIntLE 4 bytes
  let (instrumentId, bytes) ← decodeUIntLE 4 bytes
  let (reservedA, bytes) ← Alpha.decode 1 bytes
  let (reservedB, bytes) ← Alpha.decode 1 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (addOrderFlags, bytes) ← decodeUIntLE 1 bytes
  let (reserved10, bytes) ← Alpha.decode 10 bytes
  pure ({ nanosecond, orderId, side, quantity, instrumentId, reservedA, reservedB, price, addOrderFlags, reserved10 }, bytes)

@[simp] theorem encode_length (message : AddOrderMessage) : (encode message).length = 42 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Side.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : AddOrderMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : AddOrderMessage) (rest : List UInt8) :
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

end AddOrderMessage

/-- Add Attributed Order Message: 43 bytes -/
structure AddAttributedOrderMessage where
  nanosecond : BitVec 32
  orderId : BitVec 64
  side : Side
  quantity : BitVec 32
  instrumentId : BitVec 32
  reservedA : Alpha 1
  reservedB : Alpha 1
  price : BitVec 64
  attribution : Alpha 11
  addAttributedOrderFlags : BitVec 8
  deriving DecidableEq, Repr

namespace AddAttributedOrderMessage

def encode (message : AddAttributedOrderMessage) : List UInt8 :=
  encodeUIntLE 4 message.nanosecond
    ++ (encodeUIntLE 8 message.orderId
    ++ (Side.encode message.side
    ++ (encodeUIntLE 4 message.quantity
    ++ (encodeUIntLE 4 message.instrumentId
    ++ (Alpha.encode message.reservedA
    ++ (Alpha.encode message.reservedB
    ++ (encodeUIntLE 8 message.price
    ++ (Alpha.encode message.attribution
    ++ (encodeUIntLE 1 message.addAttributedOrderFlags)))))))))

def decode (bytes : List UInt8) : Option (AddAttributedOrderMessage × List UInt8) := do
  let (nanosecond, bytes) ← decodeUIntLE 4 bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (side, bytes) ← Side.decode bytes
  let (quantity, bytes) ← decodeUIntLE 4 bytes
  let (instrumentId, bytes) ← decodeUIntLE 4 bytes
  let (reservedA, bytes) ← Alpha.decode 1 bytes
  let (reservedB, bytes) ← Alpha.decode 1 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (attribution, bytes) ← Alpha.decode 11 bytes
  let (addAttributedOrderFlags, bytes) ← decodeUIntLE 1 bytes
  pure ({ nanosecond, orderId, side, quantity, instrumentId, reservedA, reservedB, price, attribution, addAttributedOrderFlags }, bytes)

@[simp] theorem encode_length (message : AddAttributedOrderMessage) : (encode message).length = 43 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Side.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : AddAttributedOrderMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : AddAttributedOrderMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end AddAttributedOrderMessage

/-- Order Deleted Message: 17 bytes -/
structure OrderDeletedMessage where
  nanosecond : BitVec 32
  orderId : BitVec 64
  orderDeletedFlags : BitVec 8
  instrumentId : BitVec 32
  deriving DecidableEq, Repr

namespace OrderDeletedMessage

def encode (message : OrderDeletedMessage) : List UInt8 :=
  encodeUIntLE 4 message.nanosecond
    ++ (encodeUIntLE 8 message.orderId
    ++ (encodeUIntLE 1 message.orderDeletedFlags
    ++ (encodeUIntLE 4 message.instrumentId)))

def decode (bytes : List UInt8) : Option (OrderDeletedMessage × List UInt8) := do
  let (nanosecond, bytes) ← decodeUIntLE 4 bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (orderDeletedFlags, bytes) ← decodeUIntLE 1 bytes
  let (instrumentId, bytes) ← decodeUIntLE 4 bytes
  pure ({ nanosecond, orderId, orderDeletedFlags, instrumentId }, bytes)

@[simp] theorem encode_length (message : OrderDeletedMessage) : (encode message).length = 17 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : OrderDeletedMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderDeletedMessage) (rest : List UInt8) :
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

end OrderDeletedMessage

/-- Order Modified Message: 25 bytes -/
structure OrderModifiedMessage where
  nanosecond : BitVec 32
  orderId : BitVec 64
  newQuantity : BitVec 32
  newPrice : BitVec 64
  orderModifiedFlags : BitVec 8
  deriving DecidableEq, Repr

namespace OrderModifiedMessage

def encode (message : OrderModifiedMessage) : List UInt8 :=
  encodeUIntLE 4 message.nanosecond
    ++ (encodeUIntLE 8 message.orderId
    ++ (encodeUIntLE 4 message.newQuantity
    ++ (encodeUIntLE 8 message.newPrice
    ++ (encodeUIntLE 1 message.orderModifiedFlags))))

def decode (bytes : List UInt8) : Option (OrderModifiedMessage × List UInt8) := do
  let (nanosecond, bytes) ← decodeUIntLE 4 bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (newQuantity, bytes) ← decodeUIntLE 4 bytes
  let (newPrice, bytes) ← decodeUIntLE 8 bytes
  let (orderModifiedFlags, bytes) ← decodeUIntLE 1 bytes
  pure ({ nanosecond, orderId, newQuantity, newPrice, orderModifiedFlags }, bytes)

@[simp] theorem encode_length (message : OrderModifiedMessage) : (encode message).length = 25 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : OrderModifiedMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderModifiedMessage) (rest : List UInt8) :
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

end OrderModifiedMessage

/-- Order Book Clear Message: 11 bytes -/
structure OrderBookClearMessage where
  nanosecond : BitVec 32
  instrumentId : BitVec 32
  reservedA : Alpha 1
  reservedB : Alpha 1
  orderBookClearFlags : BitVec 8
  deriving DecidableEq, Repr

namespace OrderBookClearMessage

def encode (message : OrderBookClearMessage) : List UInt8 :=
  encodeUIntLE 4 message.nanosecond
    ++ (encodeUIntLE 4 message.instrumentId
    ++ (Alpha.encode message.reservedA
    ++ (Alpha.encode message.reservedB
    ++ (encodeUIntLE 1 message.orderBookClearFlags))))

def decode (bytes : List UInt8) : Option (OrderBookClearMessage × List UInt8) := do
  let (nanosecond, bytes) ← decodeUIntLE 4 bytes
  let (instrumentId, bytes) ← decodeUIntLE 4 bytes
  let (reservedA, bytes) ← Alpha.decode 1 bytes
  let (reservedB, bytes) ← Alpha.decode 1 bytes
  let (orderBookClearFlags, bytes) ← decodeUIntLE 1 bytes
  pure ({ nanosecond, instrumentId, reservedA, reservedB, orderBookClearFlags }, bytes)

@[simp] theorem encode_length (message : OrderBookClearMessage) : (encode message).length = 11 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end OrderBookClearMessage

/-- Order Executed Message: 24 bytes -/
structure OrderExecutedMessage where
  nanosecond : BitVec 32
  orderId : BitVec 64
  executedQuantity : BitVec 32
  tradeMatchId : BitVec 64
  deriving DecidableEq, Repr

namespace OrderExecutedMessage

def encode (message : OrderExecutedMessage) : List UInt8 :=
  encodeUIntLE 4 message.nanosecond
    ++ (encodeUIntLE 8 message.orderId
    ++ (encodeUIntLE 4 message.executedQuantity
    ++ (encodeUIntLE 8 message.tradeMatchId)))

def decode (bytes : List UInt8) : Option (OrderExecutedMessage × List UInt8) := do
  let (nanosecond, bytes) ← decodeUIntLE 4 bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (executedQuantity, bytes) ← decodeUIntLE 4 bytes
  let (tradeMatchId, bytes) ← decodeUIntLE 8 bytes
  pure ({ nanosecond, orderId, executedQuantity, tradeMatchId }, bytes)

@[simp] theorem encode_length (message : OrderExecutedMessage) : (encode message).length = 24 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : OrderExecutedMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderExecutedMessage) (rest : List UInt8) :
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

end OrderExecutedMessage

/-- Order Executed With Price Size Message: 37 bytes -/
structure OrderExecutedWithPriceSizeMessage where
  nanosecond : BitVec 32
  orderId : BitVec 64
  executedQuantity : BitVec 32
  displayQuantity : BitVec 32
  tradeMatchId : BitVec 64
  printable : Printable
  price : BitVec 64
  deriving DecidableEq, Repr

namespace OrderExecutedWithPriceSizeMessage

def encode (message : OrderExecutedWithPriceSizeMessage) : List UInt8 :=
  encodeUIntLE 4 message.nanosecond
    ++ (encodeUIntLE 8 message.orderId
    ++ (encodeUIntLE 4 message.executedQuantity
    ++ (encodeUIntLE 4 message.displayQuantity
    ++ (encodeUIntLE 8 message.tradeMatchId
    ++ (Printable.encode message.printable
    ++ (encodeUIntLE 8 message.price))))))

def decode (bytes : List UInt8) : Option (OrderExecutedWithPriceSizeMessage × List UInt8) := do
  let (nanosecond, bytes) ← decodeUIntLE 4 bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (executedQuantity, bytes) ← decodeUIntLE 4 bytes
  let (displayQuantity, bytes) ← decodeUIntLE 4 bytes
  let (tradeMatchId, bytes) ← decodeUIntLE 8 bytes
  let (printable_, bytes) ← Printable.decode bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  pure ({ nanosecond, orderId, executedQuantity, displayQuantity, tradeMatchId, printable := printable_, price }, bytes)

@[simp] theorem encode_length (message : OrderExecutedWithPriceSizeMessage) : (encode message).length = 37 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Printable.encode_length]

theorem encode_length_pos (message : OrderExecutedWithPriceSizeMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderExecutedWithPriceSizeMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, Printable.decode_encode, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end OrderExecutedWithPriceSizeMessage

/-- Trade Message: 33 bytes -/
structure TradeMessage where
  nanosecond : BitVec 32
  executedQuantity : BitVec 32
  instrumentId : BitVec 32
  reservedA : Alpha 1
  reservedB : Alpha 1
  price : BitVec 64
  tradeMatchId : BitVec 64
  crossType : BitVec 8
  subBook : BitVec 8
  ptModFlags : BitVec 8
  deriving DecidableEq, Repr

namespace TradeMessage

def encode (message : TradeMessage) : List UInt8 :=
  encodeUIntLE 4 message.nanosecond
    ++ (encodeUIntLE 4 message.executedQuantity
    ++ (encodeUIntLE 4 message.instrumentId
    ++ (Alpha.encode message.reservedA
    ++ (Alpha.encode message.reservedB
    ++ (encodeUIntLE 8 message.price
    ++ (encodeUIntLE 8 message.tradeMatchId
    ++ (encodeUIntLE 1 message.crossType
    ++ (encodeUIntLE 1 message.subBook
    ++ (encodeUIntLE 1 message.ptModFlags)))))))))

def decode (bytes : List UInt8) : Option (TradeMessage × List UInt8) := do
  let (nanosecond, bytes) ← decodeUIntLE 4 bytes
  let (executedQuantity, bytes) ← decodeUIntLE 4 bytes
  let (instrumentId, bytes) ← decodeUIntLE 4 bytes
  let (reservedA, bytes) ← Alpha.decode 1 bytes
  let (reservedB, bytes) ← Alpha.decode 1 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (tradeMatchId, bytes) ← decodeUIntLE 8 bytes
  let (crossType, bytes) ← decodeUIntLE 1 bytes
  let (subBook, bytes) ← decodeUIntLE 1 bytes
  let (ptModFlags, bytes) ← decodeUIntLE 1 bytes
  pure ({ nanosecond, executedQuantity, instrumentId, reservedA, reservedB, price, tradeMatchId, crossType, subBook, ptModFlags }, bytes)

@[simp] theorem encode_length (message : TradeMessage) : (encode message).length = 33 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

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
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end TradeMessage

/-- Auction Trade Message: 32 bytes -/
structure AuctionTradeMessage where
  nanosecond : BitVec 32
  quantity : BitVec 32
  instrumentId : BitVec 32
  reservedA : Alpha 1
  reservedB : Alpha 1
  price : BitVec 64
  tradeMatchId : BitVec 64
  auctionType : AuctionType
  ptModFlags : BitVec 8
  deriving DecidableEq, Repr

namespace AuctionTradeMessage

def encode (message : AuctionTradeMessage) : List UInt8 :=
  encodeUIntLE 4 message.nanosecond
    ++ (encodeUIntLE 4 message.quantity
    ++ (encodeUIntLE 4 message.instrumentId
    ++ (Alpha.encode message.reservedA
    ++ (Alpha.encode message.reservedB
    ++ (encodeUIntLE 8 message.price
    ++ (encodeUIntLE 8 message.tradeMatchId
    ++ (AuctionType.encode message.auctionType
    ++ (encodeUIntLE 1 message.ptModFlags))))))))

def decode (bytes : List UInt8) : Option (AuctionTradeMessage × List UInt8) := do
  let (nanosecond, bytes) ← decodeUIntLE 4 bytes
  let (quantity, bytes) ← decodeUIntLE 4 bytes
  let (instrumentId, bytes) ← decodeUIntLE 4 bytes
  let (reservedA, bytes) ← Alpha.decode 1 bytes
  let (reservedB, bytes) ← Alpha.decode 1 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (tradeMatchId, bytes) ← decodeUIntLE 8 bytes
  let (auctionType, bytes) ← AuctionType.decode bytes
  let (ptModFlags, bytes) ← decodeUIntLE 1 bytes
  pure ({ nanosecond, quantity, instrumentId, reservedA, reservedB, price, tradeMatchId, auctionType, ptModFlags }, bytes)

@[simp] theorem encode_length (message : AuctionTradeMessage) : (encode message).length = 32 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, AuctionType.encode_length]

theorem encode_length_pos (message : AuctionTradeMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : AuctionTradeMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, AuctionType.decode_encode, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end AuctionTradeMessage

/-- Auction Info Message: 28 bytes -/
structure AuctionInfoMessage where
  nanosecond : BitVec 32
  pairedQuantity : BitVec 32
  reserved4 : Alpha 4
  reserved1 : Alpha 1
  instrumentId : BitVec 32
  reservedA : Alpha 1
  reservedB : Alpha 1
  price : BitVec 64
  auctionType : AuctionType
  deriving DecidableEq, Repr

namespace AuctionInfoMessage

def encode (message : AuctionInfoMessage) : List UInt8 :=
  encodeUIntLE 4 message.nanosecond
    ++ (encodeUIntLE 4 message.pairedQuantity
    ++ (Alpha.encode message.reserved4
    ++ (Alpha.encode message.reserved1
    ++ (encodeUIntLE 4 message.instrumentId
    ++ (Alpha.encode message.reservedA
    ++ (Alpha.encode message.reservedB
    ++ (encodeUIntLE 8 message.price
    ++ (AuctionType.encode message.auctionType))))))))

def decode (bytes : List UInt8) : Option (AuctionInfoMessage × List UInt8) := do
  let (nanosecond, bytes) ← decodeUIntLE 4 bytes
  let (pairedQuantity, bytes) ← decodeUIntLE 4 bytes
  let (reserved4, bytes) ← Alpha.decode 4 bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  let (instrumentId, bytes) ← decodeUIntLE 4 bytes
  let (reservedA, bytes) ← Alpha.decode 1 bytes
  let (reservedB, bytes) ← Alpha.decode 1 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (auctionType, bytes) ← AuctionType.decode bytes
  pure ({ nanosecond, pairedQuantity, reserved4, reserved1, instrumentId, reservedA, reservedB, price, auctionType }, bytes)

@[simp] theorem encode_length (message : AuctionInfoMessage) : (encode message).length = 28 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, AuctionType.encode_length]

theorem encode_length_pos (message : AuctionInfoMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : AuctionInfoMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [AuctionType.decode_encode, some_bind]
  rfl

end AuctionInfoMessage

/-- Statistics Message: 21 bytes -/
structure StatisticsMessage where
  nanosecond : BitVec 32
  instrumentId : BitVec 32
  reservedA : Alpha 1
  reservedB : Alpha 1
  statisticType : StatisticType
  price : BitVec 64
  openClosePriceIndicator : OpenClosePriceIndicator
  statisticsReserved : BitVec 8
  deriving DecidableEq, Repr

namespace StatisticsMessage

def encode (message : StatisticsMessage) : List UInt8 :=
  encodeUIntLE 4 message.nanosecond
    ++ (encodeUIntLE 4 message.instrumentId
    ++ (Alpha.encode message.reservedA
    ++ (Alpha.encode message.reservedB
    ++ (StatisticType.encode message.statisticType
    ++ (encodeUIntLE 8 message.price
    ++ (OpenClosePriceIndicator.encode message.openClosePriceIndicator
    ++ (encodeUIntLE 1 message.statisticsReserved)))))))

def decode (bytes : List UInt8) : Option (StatisticsMessage × List UInt8) := do
  let (nanosecond, bytes) ← decodeUIntLE 4 bytes
  let (instrumentId, bytes) ← decodeUIntLE 4 bytes
  let (reservedA, bytes) ← Alpha.decode 1 bytes
  let (reservedB, bytes) ← Alpha.decode 1 bytes
  let (statisticType, bytes) ← StatisticType.decode bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (openClosePriceIndicator, bytes) ← OpenClosePriceIndicator.decode bytes
  let (statisticsReserved, bytes) ← decodeUIntLE 1 bytes
  pure ({ nanosecond, instrumentId, reservedA, reservedB, statisticType, price, openClosePriceIndicator, statisticsReserved }, bytes)

@[simp] theorem encode_length (message : StatisticsMessage) : (encode message).length = 21 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, StatisticType.encode_length, OpenClosePriceIndicator.encode_length]

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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, StatisticType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, OpenClosePriceIndicator.decode_encode, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end StatisticsMessage

/-- Top Of Book Message: 32 bytes -/
structure TopOfBookMessage where
  nanosecond : BitVec 32
  instrumentId : BitVec 32
  buyLimitPrice : BitVec 64
  buyLimitSize : BitVec 32
  sellLimitPrice : BitVec 64
  sellLimitSize : BitVec 32
  deriving DecidableEq, Repr

namespace TopOfBookMessage

def encode (message : TopOfBookMessage) : List UInt8 :=
  encodeUIntLE 4 message.nanosecond
    ++ (encodeUIntLE 4 message.instrumentId
    ++ (encodeUIntLE 8 message.buyLimitPrice
    ++ (encodeUIntLE 4 message.buyLimitSize
    ++ (encodeUIntLE 8 message.sellLimitPrice
    ++ (encodeUIntLE 4 message.sellLimitSize)))))

def decode (bytes : List UInt8) : Option (TopOfBookMessage × List UInt8) := do
  let (nanosecond, bytes) ← decodeUIntLE 4 bytes
  let (instrumentId, bytes) ← decodeUIntLE 4 bytes
  let (buyLimitPrice, bytes) ← decodeUIntLE 8 bytes
  let (buyLimitSize, bytes) ← decodeUIntLE 4 bytes
  let (sellLimitPrice, bytes) ← decodeUIntLE 8 bytes
  let (sellLimitSize, bytes) ← decodeUIntLE 4 bytes
  pure ({ nanosecond, instrumentId, buyLimitPrice, buyLimitSize, sellLimitPrice, sellLimitSize }, bytes)

@[simp] theorem encode_length (message : TopOfBookMessage) : (encode message).length = 32 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

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
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end TopOfBookMessage

/-- Any Payload, selected by Message Type -/
inductive Payload where
  | loginRequestMessage (message : LoginRequestMessage) -- 1
  | loginResponseMessage (message : LoginResponseMessage) -- 2
  | replayRequestMessage (message : ReplayRequestMessage) -- 3
  | replayResponseMessage (message : ReplayResponseMessage) -- 4
  | timeMessage (message : TimeMessage) -- 84
  | systemEventMessage (message : SystemEventMessage) -- 83
  | symbolDirectoryMessage (message : SymbolDirectoryMessage) -- 82
  | symbolStatusMessage (message : SymbolStatusMessage) -- 72
  | addOrderMessage (message : AddOrderMessage) -- 65
  | addAttributedOrderMessage (message : AddAttributedOrderMessage) -- 70
  | orderDeletedMessage (message : OrderDeletedMessage) -- 68
  | orderModifiedMessage (message : OrderModifiedMessage) -- 85
  | orderBookClearMessage (message : OrderBookClearMessage) -- 121
  | orderExecutedMessage (message : OrderExecutedMessage) -- 69
  | orderExecutedWithPriceSizeMessage (message : OrderExecutedWithPriceSizeMessage) -- 67
  | tradeMessage (message : TradeMessage) -- 80
  | auctionTradeMessage (message : AuctionTradeMessage) -- 81
  | auctionInfoMessage (message : AuctionInfoMessage) -- 73
  | statisticsMessage (message : StatisticsMessage) -- 119
  | topOfBookMessage (message : TopOfBookMessage) -- 113
  deriving DecidableEq, Repr

namespace Payload

/-- The Message Type each message is sent under -/
def tag : Payload → BitVec 8
  | .loginRequestMessage _ => 1
  | .loginResponseMessage _ => 2
  | .replayRequestMessage _ => 3
  | .replayResponseMessage _ => 4
  | .timeMessage _ => 84
  | .systemEventMessage _ => 83
  | .symbolDirectoryMessage _ => 82
  | .symbolStatusMessage _ => 72
  | .addOrderMessage _ => 65
  | .addAttributedOrderMessage _ => 70
  | .orderDeletedMessage _ => 68
  | .orderModifiedMessage _ => 85
  | .orderBookClearMessage _ => 121
  | .orderExecutedMessage _ => 69
  | .orderExecutedWithPriceSizeMessage _ => 67
  | .tradeMessage _ => 80
  | .auctionTradeMessage _ => 81
  | .auctionInfoMessage _ => 73
  | .statisticsMessage _ => 119
  | .topOfBookMessage _ => 113

def encode : Payload → List UInt8
  | .loginRequestMessage message => LoginRequestMessage.encode message
  | .loginResponseMessage message => LoginResponseMessage.encode message
  | .replayRequestMessage message => ReplayRequestMessage.encode message
  | .replayResponseMessage message => ReplayResponseMessage.encode message
  | .timeMessage message => TimeMessage.encode message
  | .systemEventMessage message => SystemEventMessage.encode message
  | .symbolDirectoryMessage message => SymbolDirectoryMessage.encode message
  | .symbolStatusMessage message => SymbolStatusMessage.encode message
  | .addOrderMessage message => AddOrderMessage.encode message
  | .addAttributedOrderMessage message => AddAttributedOrderMessage.encode message
  | .orderDeletedMessage message => OrderDeletedMessage.encode message
  | .orderModifiedMessage message => OrderModifiedMessage.encode message
  | .orderBookClearMessage message => OrderBookClearMessage.encode message
  | .orderExecutedMessage message => OrderExecutedMessage.encode message
  | .orderExecutedWithPriceSizeMessage message => OrderExecutedWithPriceSizeMessage.encode message
  | .tradeMessage message => TradeMessage.encode message
  | .auctionTradeMessage message => AuctionTradeMessage.encode message
  | .auctionInfoMessage message => AuctionInfoMessage.encode message
  | .statisticsMessage message => StatisticsMessage.encode message
  | .topOfBookMessage message => TopOfBookMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : Payload) : (encode message).length ≤ 63 := by
  cases message with
  | loginRequestMessage inner =>
    simp only [encode, LoginRequestMessage.encode_length]
    omega
  | loginResponseMessage inner =>
    simp only [encode, LoginResponseMessage.encode_length]
    omega
  | replayRequestMessage inner =>
    simp only [encode, ReplayRequestMessage.encode_length]
    omega
  | replayResponseMessage inner =>
    simp only [encode, ReplayResponseMessage.encode_length]
    omega
  | timeMessage inner =>
    simp only [encode, TimeMessage.encode_length]
    omega
  | systemEventMessage inner =>
    simp only [encode, SystemEventMessage.encode_length]
    omega
  | symbolDirectoryMessage inner =>
    simp only [encode, SymbolDirectoryMessage.encode_length]
    omega
  | symbolStatusMessage inner =>
    simp only [encode, SymbolStatusMessage.encode_length]
    omega
  | addOrderMessage inner =>
    simp only [encode, AddOrderMessage.encode_length]
    omega
  | addAttributedOrderMessage inner =>
    simp only [encode, AddAttributedOrderMessage.encode_length]
    omega
  | orderDeletedMessage inner =>
    simp only [encode, OrderDeletedMessage.encode_length]
    omega
  | orderModifiedMessage inner =>
    simp only [encode, OrderModifiedMessage.encode_length]
    omega
  | orderBookClearMessage inner =>
    simp only [encode, OrderBookClearMessage.encode_length]
    omega
  | orderExecutedMessage inner =>
    simp only [encode, OrderExecutedMessage.encode_length]
    omega
  | orderExecutedWithPriceSizeMessage inner =>
    simp only [encode, OrderExecutedWithPriceSizeMessage.encode_length]
    omega
  | tradeMessage inner =>
    simp only [encode, TradeMessage.encode_length]
    omega
  | auctionTradeMessage inner =>
    simp only [encode, AuctionTradeMessage.encode_length]
    omega
  | auctionInfoMessage inner =>
    simp only [encode, AuctionInfoMessage.encode_length]
    omega
  | statisticsMessage inner =>
    simp only [encode, StatisticsMessage.encode_length]
    omega
  | topOfBookMessage inner =>
    simp only [encode, TopOfBookMessage.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (Payload × List UInt8) :=
  if tag = 1 then (LoginRequestMessage.decode bytes).map fun (message, rest) => (.loginRequestMessage message, rest)
  else if tag = 2 then (LoginResponseMessage.decode bytes).map fun (message, rest) => (.loginResponseMessage message, rest)
  else if tag = 3 then (ReplayRequestMessage.decode bytes).map fun (message, rest) => (.replayRequestMessage message, rest)
  else if tag = 4 then (ReplayResponseMessage.decode bytes).map fun (message, rest) => (.replayResponseMessage message, rest)
  else if tag = 84 then (TimeMessage.decode bytes).map fun (message, rest) => (.timeMessage message, rest)
  else if tag = 83 then (SystemEventMessage.decode bytes).map fun (message, rest) => (.systemEventMessage message, rest)
  else if tag = 82 then (SymbolDirectoryMessage.decode bytes).map fun (message, rest) => (.symbolDirectoryMessage message, rest)
  else if tag = 72 then (SymbolStatusMessage.decode bytes).map fun (message, rest) => (.symbolStatusMessage message, rest)
  else if tag = 65 then (AddOrderMessage.decode bytes).map fun (message, rest) => (.addOrderMessage message, rest)
  else if tag = 70 then (AddAttributedOrderMessage.decode bytes).map fun (message, rest) => (.addAttributedOrderMessage message, rest)
  else if tag = 68 then (OrderDeletedMessage.decode bytes).map fun (message, rest) => (.orderDeletedMessage message, rest)
  else if tag = 85 then (OrderModifiedMessage.decode bytes).map fun (message, rest) => (.orderModifiedMessage message, rest)
  else if tag = 121 then (OrderBookClearMessage.decode bytes).map fun (message, rest) => (.orderBookClearMessage message, rest)
  else if tag = 69 then (OrderExecutedMessage.decode bytes).map fun (message, rest) => (.orderExecutedMessage message, rest)
  else if tag = 67 then (OrderExecutedWithPriceSizeMessage.decode bytes).map fun (message, rest) => (.orderExecutedWithPriceSizeMessage message, rest)
  else if tag = 80 then (TradeMessage.decode bytes).map fun (message, rest) => (.tradeMessage message, rest)
  else if tag = 81 then (AuctionTradeMessage.decode bytes).map fun (message, rest) => (.auctionTradeMessage message, rest)
  else if tag = 73 then (AuctionInfoMessage.decode bytes).map fun (message, rest) => (.auctionInfoMessage message, rest)
  else if tag = 119 then (StatisticsMessage.decode bytes).map fun (message, rest) => (.statisticsMessage message, rest)
  else if tag = 113 then (TopOfBookMessage.decode bytes).map fun (message, rest) => (.topOfBookMessage message, rest)
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
theorem encodeBody_length_lt (message : Message) : (encodeBody message).length + 1 < 256 ^ 1 := by
  unfold encodeBody
  cases message.payload with
  | loginRequestMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, LoginRequestMessage.encode_length]
    omega
  | loginResponseMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, LoginResponseMessage.encode_length]
    omega
  | replayRequestMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, ReplayRequestMessage.encode_length]
    omega
  | replayResponseMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, ReplayResponseMessage.encode_length]
    omega
  | timeMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, TimeMessage.encode_length]
    omega
  | systemEventMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, SystemEventMessage.encode_length]
    omega
  | symbolDirectoryMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, SymbolDirectoryMessage.encode_length]
    omega
  | symbolStatusMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, SymbolStatusMessage.encode_length]
    omega
  | addOrderMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, AddOrderMessage.encode_length]
    omega
  | addAttributedOrderMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, AddAttributedOrderMessage.encode_length]
    omega
  | orderDeletedMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, OrderDeletedMessage.encode_length]
    omega
  | orderModifiedMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, OrderModifiedMessage.encode_length]
    omega
  | orderBookClearMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, OrderBookClearMessage.encode_length]
    omega
  | orderExecutedMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, OrderExecutedMessage.encode_length]
    omega
  | orderExecutedWithPriceSizeMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, OrderExecutedWithPriceSizeMessage.encode_length]
    omega
  | tradeMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, TradeMessage.encode_length]
    omega
  | auctionTradeMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, AuctionTradeMessage.encode_length]
    omega
  | auctionInfoMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, AuctionInfoMessage.encode_length]
    omega
  | statisticsMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, StatisticsMessage.encode_length]
    omega
  | topOfBookMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, TopOfBookMessage.encode_length]
    omega

/-- Size rule: Message Length counts the bytes after it plus 1, so it is written from the body and checked on decode -/
def encode : Message → List UInt8 :=
  encodeFramedLE 1 1 encodeBody

def decode : List UInt8 → Option (Message × List UInt8) :=
  decodeFramedLE 1 1 decodeBody

@[simp] theorem decode_encode (message : Message) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) :=
  decodeFramedLE_encodeFramedLE 1 1 encodeBody decodeBody message (decodeBody_encodeBody message) (encodeBody_length_lt message) rest

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

end Omi.LsegMillenniumLevel2replayMitchV119
