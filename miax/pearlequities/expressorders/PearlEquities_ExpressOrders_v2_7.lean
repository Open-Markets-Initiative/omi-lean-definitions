import Omi.Wire

/-!
# Miami International Holdings Express Orders v2.7

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Note: New Order Instructions is a bit field set, proven as its 2 byte integer rather than bit by bit.

Note: Self Trade Protection is a bit field set, proven as its 1 byte integer rather than bit by bit.

Note: Routing is a bit field set, proven as its 1 byte integer rather than bit by bit.

Note: Modify Order Instructions is a bit field set, proven as its 1 byte integer rather than bit by bit.

Note: Order Execution Instructions is a bit field set, proven as its 2 byte integer rather than bit by bit.

Note: Additional Liquidity Indicator is a bit field set, proven as its 1 byte integer rather than bit by bit.

Note: Sequenced Data Packet is not framed: its length Esesm Packet Length is not an integer it reads.

Note: Purge Instructions is a bit field set, proven as its 2 byte integer rather than bit by bit.

Note: Unsequenced Data Packet is not framed: its length Esesm Packet Length is not an integer it reads.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.MiaxPearlequitiesExpressordersMeoV27

/-- Test Security Indicator: one byte code -/
def TestSecurityIndicator.codes : List UInt8 :=
  [0x59, 0x4E]

inductive TestSecurityIndicator where
  | yes -- Yes
  | no -- No
  | unlisted (byte : { byte : UInt8 // byte ∉ TestSecurityIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TestSecurityIndicator

def toByte : TestSecurityIndicator → UInt8
  | .yes => 0x59
  | .no => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TestSecurityIndicator :=
  if byte = 0x59 then .yes
  else .no

def ofByte (byte : UInt8) : TestSecurityIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TestSecurityIndicator) : ofByte value.toByte = value := by
  cases value with
  | yes => decide
  | no => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : TestSecurityIndicator) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (TestSecurityIndicator × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : TestSecurityIndicator) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : TestSecurityIndicator) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end TestSecurityIndicator

/-- Primary Market Code: one byte code -/
def PrimaryMarketCode.codes : List UInt8 :=
  [0x41, 0x42, 0x43, 0x48, 0x49, 0x4A, 0x4B, 0x4C, 0x4D, 0x4E, 0x50, 0x51, 0x55, 0x56, 0x58, 0x59, 0x5A]

inductive PrimaryMarketCode where
  | nyseAmerican -- Nyse American
  | nasdaqBx -- Nasdaq Bx
  | nyseNational -- Nyse National
  | miaxPearlEquities -- Miax Pearl Equities
  | nasdaqIse -- Nasdaq Ise
  | cboeEdgaExchange -- Cboe Edga Exchange
  | cboeEdgxExchange -- Cboe Edgx Exchange
  | longTermStockExchange -- Long Term Stock Exchange
  | nyseChicago -- Nyse Chicago
  | newYorkStockExchange -- New York Stock Exchange
  | nyseArca -- Nyse Arca
  | nasdaq -- Nasdaq
  | membersExchange -- Members Exchange
  | investorsExchange -- Investors Exchange
  | nasdaqPhlx -- Nasdaq Phlx
  | cboeByxExchange -- Cboe Byx Exchange
  | cboeBzxExchange -- Cboe Bzx Exchange
  | unlisted (byte : { byte : UInt8 // byte ∉ PrimaryMarketCode.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace PrimaryMarketCode

def toByte : PrimaryMarketCode → UInt8
  | .nyseAmerican => 0x41
  | .nasdaqBx => 0x42
  | .nyseNational => 0x43
  | .miaxPearlEquities => 0x48
  | .nasdaqIse => 0x49
  | .cboeEdgaExchange => 0x4A
  | .cboeEdgxExchange => 0x4B
  | .longTermStockExchange => 0x4C
  | .nyseChicago => 0x4D
  | .newYorkStockExchange => 0x4E
  | .nyseArca => 0x50
  | .nasdaq => 0x51
  | .membersExchange => 0x55
  | .investorsExchange => 0x56
  | .nasdaqPhlx => 0x58
  | .cboeByxExchange => 0x59
  | .cboeBzxExchange => 0x5A
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : PrimaryMarketCode :=
  if byte = 0x41 then .nyseAmerican
  else if byte = 0x42 then .nasdaqBx
  else if byte = 0x43 then .nyseNational
  else if byte = 0x48 then .miaxPearlEquities
  else if byte = 0x49 then .nasdaqIse
  else if byte = 0x4A then .cboeEdgaExchange
  else if byte = 0x4B then .cboeEdgxExchange
  else if byte = 0x4C then .longTermStockExchange
  else if byte = 0x4D then .nyseChicago
  else if byte = 0x4E then .newYorkStockExchange
  else if byte = 0x50 then .nyseArca
  else if byte = 0x51 then .nasdaq
  else if byte = 0x55 then .membersExchange
  else if byte = 0x56 then .investorsExchange
  else if byte = 0x58 then .nasdaqPhlx
  else if byte = 0x59 then .cboeByxExchange
  else .cboeBzxExchange

def ofByte (byte : UInt8) : PrimaryMarketCode :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : PrimaryMarketCode) : ofByte value.toByte = value := by
  cases value with
  | nyseAmerican => decide
  | nasdaqBx => decide
  | nyseNational => decide
  | miaxPearlEquities => decide
  | nasdaqIse => decide
  | cboeEdgaExchange => decide
  | cboeEdgxExchange => decide
  | longTermStockExchange => decide
  | nyseChicago => decide
  | newYorkStockExchange => decide
  | nyseArca => decide
  | nasdaq => decide
  | membersExchange => decide
  | investorsExchange => decide
  | nasdaqPhlx => decide
  | cboeByxExchange => decide
  | cboeBzxExchange => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : PrimaryMarketCode) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (PrimaryMarketCode × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : PrimaryMarketCode) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : PrimaryMarketCode) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end PrimaryMarketCode

/-- Order Status: one byte code -/
def OrderStatus.codes : List UInt8 :=
  [0x41, 0x42, 0x43, 0x44, 0x45, 0x46, 0x47, 0x48, 0x49, 0x4A, 0x4B, 0x4C, 0x4D, 0x4E, 0x4F, 0x50, 0x51, 0x52, 0x53, 0x54, 0x55, 0x56, 0x57, 0x58, 0x59, 0x5A, 0x61, 0x62, 0x63, 0x64, 0x65, 0x66, 0x67, 0x68, 0x69, 0x6A, 0x6B, 0x6C, 0x6D, 0x6E, 0x6F, 0x70, 0x71, 0x72, 0x73, 0x74, 0x75, 0x76, 0x77, 0x78, 0x79, 0x7A, 0x30, 0x31, 0x32, 0x33, 0x34, 0x35, 0x36, 0x37, 0x38, 0x39, 0x21, 0x40, 0x23, 0x24, 0x2A]

inductive OrderStatus where
  | duplicateClientOrderId -- Duplicate Client Order Id
  | notInLiveOrderWindow -- Not In Live Order Window
  | matchingEngineIsNotAvailable -- Matching Engine Is Not Available
  | duplicateOrderCheckRejected -- Duplicate Order Check Rejected
  | exceededTestSymbolThrottle -- Exceeded Test Symbol Throttle
  | isoOrdersNotAllowed -- Iso Orders Not Allowed
  | invalidSelfTradeProtectionGroupOrItsUse -- Invalid Self Trade Protection Group Or Its Use
  | blockedByMeoUser -- Blocked By Meo User
  | invalidMpid -- Invalid Mpid
  | invalidPrice -- Invalid Price
  | invalidSize -- Invalid Size
  | blockedByFirmOverMiaxMemberFirm -- Blocked By Firm Over Miax Member Firm
  | exceededMaxAllowedSize -- Exceeded Max Allowed Size
  | exceededMaxNotionalValue -- Exceeded Max Notional Value
  | invalidClientOrderId -- Invalid Client Order Id
  | requestIsNotPermittedForThisSession -- Request Is Not Permitted For This Session
  | shortSaleOrdersNotAllowed -- Short Sale Orders Not Allowed
  | blockedByCumulativeRiskMetrics -- Blocked By Cumulative Risk Metrics
  | invalidSymbolId -- Invalid Symbol Id
  | invalidOrderType -- Invalid Order Type
  | invalidUseOfLocateRequired -- Invalid Use Of Locate Required
  | invalidSellShort -- Invalid Sell Short
  | limitOrderPriceProtection -- Limit Order Price Protection
  | mpidNotPermitted -- Mpid Not Permitted
  | isoAttributeNotCompatibleWithTheOrderType -- Iso Attribute Not Compatible With The Order Type
  | undefinedReason -- Undefined Reason
  | invalidCapacity -- Invalid Capacity
  | invalidTimeInForce -- Invalid Time In Force
  | invalidRoutingInstructionOrUse -- Invalid Routing Instruction Or Use
  | invalidSelfTradeProtectionLevel -- Invalid Self Trade Protection Level
  | invalidSelfTradeProtectionInstructionOrUse -- Invalid Self Trade Protection Instruction Or Use
  | invalidAttributableValueOrUse -- Invalid Attributable Value Or Use
  | invalidPriceSlidingAndRepriceFrequencyValueOrUse -- Invalid Price Sliding And Reprice Frequency Value Or Use
  | invalidUseOfPostOnlyInstruction -- Invalid Use Of Post Only Instruction
  | invalidUseOfDisplayInstruction -- Invalid Use Of Display Instruction
  | invalidValueOrUseForAvailableWhenLocked -- Invalid Value Or Use For Available When Locked
  | marketOrderPriceProtection -- Market Order Price Protection
  | invalidRoutingStrategyOrItsUse -- Invalid Routing Strategy Or Its Use
  | invalidValueInAccount -- Invalid Value In Account
  | invalidValueInClearingAccount -- Invalid Value In Clearing Account
  | invalidUseOfTradingCollarDollarValue -- Invalid Use Of Trading Collar Dollar Value
  | invalidForCurrentSymbolTradingStatusOrMarketState -- Invalid For Current Symbol Trading Status Or Market State
  | primaryExchangeIpoNotCompleteIpoInProgress -- Primary Exchange Ipo Not Complete Ipo In Progress
  | invalidUseOfMinQtySizeOrMinQtyExecTypeInstruction -- Invalid Use Of Min Qty Size Or Min Qty Exec Type Instruction
  | invalidUseOfOrderType -- Invalid Use Of Order Type
  | invalidMaxFloorQty -- Invalid Max Floor Qty
  | invalidDisplayRangeQty -- Invalid Display Range Qty
  | featureNotAvailable -- Feature Not Available
  | primaryListingMarketRoutingNotSupported -- Primary Listing Market Routing Not Supported
  | tooLateForPrimaryListingMarketOrder -- Too Late For Primary Listing Market Order
  | pacOrdersAreNotAllowedRoutingToPrimary -- Pac Orders Are Not Allowed Routing To Primary
  | shortSaleExemptOrdersNotAllowed -- Short Sale Exempt Orders Not Allowed
  | limitPriceMoreAggressiveThanMarketImpactCollar -- Limit Price More Aggressive Than Market Impact Collar
  | marketOrdersNotAllowed -- Market Orders Not Allowed
  | restrictedSecurityNotAllowed -- Restricted Security Not Allowed
  | blockedByOrderRateMetrics -- Blocked By Order Rate Metrics
  | averageDailyVolumeProtection -- Average Daily Volume Protection
  | invalidOffsetForPrimaryPegOrder -- Invalid Offset For Primary Peg Order
  | invalidPurgeGroupSpecified -- Invalid Purge Group Specified
  | invalidOrNotPermittedValueInLocateAccount -- Invalid Or Not Permitted Value In Locate Account
  | blockedByDropCopyAcodEvent -- Blocked By Drop Copy Acod Event
  | blockedByDropCopyAcosfEvent -- Blocked By Drop Copy Acosf Event
  | invalidUseOfCancelOrderIfNotANbboSetter -- Invalid Use Of Cancel Order If Not A Nbbo Setter
  | invalidOrderExpiryTime -- Invalid Order Expiry Time
  | earlyTradingSessionRestriction -- Early Trading Session Restriction
  | lateTradingSessionRestriction -- Late Trading Session Restriction
  | downgradedFromOlderVersion -- Downgraded From Older Version
  | unlisted (byte : { byte : UInt8 // byte ∉ OrderStatus.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OrderStatus

def toByte : OrderStatus → UInt8
  | .duplicateClientOrderId => 0x41
  | .notInLiveOrderWindow => 0x42
  | .matchingEngineIsNotAvailable => 0x43
  | .duplicateOrderCheckRejected => 0x44
  | .exceededTestSymbolThrottle => 0x45
  | .isoOrdersNotAllowed => 0x46
  | .invalidSelfTradeProtectionGroupOrItsUse => 0x47
  | .blockedByMeoUser => 0x48
  | .invalidMpid => 0x49
  | .invalidPrice => 0x4A
  | .invalidSize => 0x4B
  | .blockedByFirmOverMiaxMemberFirm => 0x4C
  | .exceededMaxAllowedSize => 0x4D
  | .exceededMaxNotionalValue => 0x4E
  | .invalidClientOrderId => 0x4F
  | .requestIsNotPermittedForThisSession => 0x50
  | .shortSaleOrdersNotAllowed => 0x51
  | .blockedByCumulativeRiskMetrics => 0x52
  | .invalidSymbolId => 0x53
  | .invalidOrderType => 0x54
  | .invalidUseOfLocateRequired => 0x55
  | .invalidSellShort => 0x56
  | .limitOrderPriceProtection => 0x57
  | .mpidNotPermitted => 0x58
  | .isoAttributeNotCompatibleWithTheOrderType => 0x59
  | .undefinedReason => 0x5A
  | .invalidCapacity => 0x61
  | .invalidTimeInForce => 0x62
  | .invalidRoutingInstructionOrUse => 0x63
  | .invalidSelfTradeProtectionLevel => 0x64
  | .invalidSelfTradeProtectionInstructionOrUse => 0x65
  | .invalidAttributableValueOrUse => 0x66
  | .invalidPriceSlidingAndRepriceFrequencyValueOrUse => 0x67
  | .invalidUseOfPostOnlyInstruction => 0x68
  | .invalidUseOfDisplayInstruction => 0x69
  | .invalidValueOrUseForAvailableWhenLocked => 0x6A
  | .marketOrderPriceProtection => 0x6B
  | .invalidRoutingStrategyOrItsUse => 0x6C
  | .invalidValueInAccount => 0x6D
  | .invalidValueInClearingAccount => 0x6E
  | .invalidUseOfTradingCollarDollarValue => 0x6F
  | .invalidForCurrentSymbolTradingStatusOrMarketState => 0x70
  | .primaryExchangeIpoNotCompleteIpoInProgress => 0x71
  | .invalidUseOfMinQtySizeOrMinQtyExecTypeInstruction => 0x72
  | .invalidUseOfOrderType => 0x73
  | .invalidMaxFloorQty => 0x74
  | .invalidDisplayRangeQty => 0x75
  | .featureNotAvailable => 0x76
  | .primaryListingMarketRoutingNotSupported => 0x77
  | .tooLateForPrimaryListingMarketOrder => 0x78
  | .pacOrdersAreNotAllowedRoutingToPrimary => 0x79
  | .shortSaleExemptOrdersNotAllowed => 0x7A
  | .limitPriceMoreAggressiveThanMarketImpactCollar => 0x30
  | .marketOrdersNotAllowed => 0x31
  | .restrictedSecurityNotAllowed => 0x32
  | .blockedByOrderRateMetrics => 0x33
  | .averageDailyVolumeProtection => 0x34
  | .invalidOffsetForPrimaryPegOrder => 0x35
  | .invalidPurgeGroupSpecified => 0x36
  | .invalidOrNotPermittedValueInLocateAccount => 0x37
  | .blockedByDropCopyAcodEvent => 0x38
  | .blockedByDropCopyAcosfEvent => 0x39
  | .invalidUseOfCancelOrderIfNotANbboSetter => 0x21
  | .invalidOrderExpiryTime => 0x40
  | .earlyTradingSessionRestriction => 0x23
  | .lateTradingSessionRestriction => 0x24
  | .downgradedFromOlderVersion => 0x2A
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OrderStatus :=
  if byte = 0x41 then .duplicateClientOrderId
  else if byte = 0x42 then .notInLiveOrderWindow
  else if byte = 0x43 then .matchingEngineIsNotAvailable
  else if byte = 0x44 then .duplicateOrderCheckRejected
  else if byte = 0x45 then .exceededTestSymbolThrottle
  else if byte = 0x46 then .isoOrdersNotAllowed
  else if byte = 0x47 then .invalidSelfTradeProtectionGroupOrItsUse
  else if byte = 0x48 then .blockedByMeoUser
  else if byte = 0x49 then .invalidMpid
  else if byte = 0x4A then .invalidPrice
  else if byte = 0x4B then .invalidSize
  else if byte = 0x4C then .blockedByFirmOverMiaxMemberFirm
  else if byte = 0x4D then .exceededMaxAllowedSize
  else if byte = 0x4E then .exceededMaxNotionalValue
  else if byte = 0x4F then .invalidClientOrderId
  else if byte = 0x50 then .requestIsNotPermittedForThisSession
  else if byte = 0x51 then .shortSaleOrdersNotAllowed
  else if byte = 0x52 then .blockedByCumulativeRiskMetrics
  else if byte = 0x53 then .invalidSymbolId
  else if byte = 0x54 then .invalidOrderType
  else if byte = 0x55 then .invalidUseOfLocateRequired
  else if byte = 0x56 then .invalidSellShort
  else if byte = 0x57 then .limitOrderPriceProtection
  else if byte = 0x58 then .mpidNotPermitted
  else if byte = 0x59 then .isoAttributeNotCompatibleWithTheOrderType
  else if byte = 0x5A then .undefinedReason
  else if byte = 0x61 then .invalidCapacity
  else if byte = 0x62 then .invalidTimeInForce
  else if byte = 0x63 then .invalidRoutingInstructionOrUse
  else if byte = 0x64 then .invalidSelfTradeProtectionLevel
  else if byte = 0x65 then .invalidSelfTradeProtectionInstructionOrUse
  else if byte = 0x66 then .invalidAttributableValueOrUse
  else if byte = 0x67 then .invalidPriceSlidingAndRepriceFrequencyValueOrUse
  else if byte = 0x68 then .invalidUseOfPostOnlyInstruction
  else if byte = 0x69 then .invalidUseOfDisplayInstruction
  else if byte = 0x6A then .invalidValueOrUseForAvailableWhenLocked
  else if byte = 0x6B then .marketOrderPriceProtection
  else if byte = 0x6C then .invalidRoutingStrategyOrItsUse
  else if byte = 0x6D then .invalidValueInAccount
  else if byte = 0x6E then .invalidValueInClearingAccount
  else if byte = 0x6F then .invalidUseOfTradingCollarDollarValue
  else if byte = 0x70 then .invalidForCurrentSymbolTradingStatusOrMarketState
  else if byte = 0x71 then .primaryExchangeIpoNotCompleteIpoInProgress
  else if byte = 0x72 then .invalidUseOfMinQtySizeOrMinQtyExecTypeInstruction
  else if byte = 0x73 then .invalidUseOfOrderType
  else if byte = 0x74 then .invalidMaxFloorQty
  else if byte = 0x75 then .invalidDisplayRangeQty
  else if byte = 0x76 then .featureNotAvailable
  else if byte = 0x77 then .primaryListingMarketRoutingNotSupported
  else if byte = 0x78 then .tooLateForPrimaryListingMarketOrder
  else if byte = 0x79 then .pacOrdersAreNotAllowedRoutingToPrimary
  else if byte = 0x7A then .shortSaleExemptOrdersNotAllowed
  else if byte = 0x30 then .limitPriceMoreAggressiveThanMarketImpactCollar
  else if byte = 0x31 then .marketOrdersNotAllowed
  else if byte = 0x32 then .restrictedSecurityNotAllowed
  else if byte = 0x33 then .blockedByOrderRateMetrics
  else if byte = 0x34 then .averageDailyVolumeProtection
  else if byte = 0x35 then .invalidOffsetForPrimaryPegOrder
  else if byte = 0x36 then .invalidPurgeGroupSpecified
  else if byte = 0x37 then .invalidOrNotPermittedValueInLocateAccount
  else if byte = 0x38 then .blockedByDropCopyAcodEvent
  else if byte = 0x39 then .blockedByDropCopyAcosfEvent
  else if byte = 0x21 then .invalidUseOfCancelOrderIfNotANbboSetter
  else if byte = 0x40 then .invalidOrderExpiryTime
  else if byte = 0x23 then .earlyTradingSessionRestriction
  else if byte = 0x24 then .lateTradingSessionRestriction
  else .downgradedFromOlderVersion

def ofByte (byte : UInt8) : OrderStatus :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OrderStatus) : ofByte value.toByte = value := by
  cases value with
  | duplicateClientOrderId => decide
  | notInLiveOrderWindow => decide
  | matchingEngineIsNotAvailable => decide
  | duplicateOrderCheckRejected => decide
  | exceededTestSymbolThrottle => decide
  | isoOrdersNotAllowed => decide
  | invalidSelfTradeProtectionGroupOrItsUse => decide
  | blockedByMeoUser => decide
  | invalidMpid => decide
  | invalidPrice => decide
  | invalidSize => decide
  | blockedByFirmOverMiaxMemberFirm => decide
  | exceededMaxAllowedSize => decide
  | exceededMaxNotionalValue => decide
  | invalidClientOrderId => decide
  | requestIsNotPermittedForThisSession => decide
  | shortSaleOrdersNotAllowed => decide
  | blockedByCumulativeRiskMetrics => decide
  | invalidSymbolId => decide
  | invalidOrderType => decide
  | invalidUseOfLocateRequired => decide
  | invalidSellShort => decide
  | limitOrderPriceProtection => decide
  | mpidNotPermitted => decide
  | isoAttributeNotCompatibleWithTheOrderType => decide
  | undefinedReason => decide
  | invalidCapacity => decide
  | invalidTimeInForce => decide
  | invalidRoutingInstructionOrUse => decide
  | invalidSelfTradeProtectionLevel => decide
  | invalidSelfTradeProtectionInstructionOrUse => decide
  | invalidAttributableValueOrUse => decide
  | invalidPriceSlidingAndRepriceFrequencyValueOrUse => decide
  | invalidUseOfPostOnlyInstruction => decide
  | invalidUseOfDisplayInstruction => decide
  | invalidValueOrUseForAvailableWhenLocked => decide
  | marketOrderPriceProtection => decide
  | invalidRoutingStrategyOrItsUse => decide
  | invalidValueInAccount => decide
  | invalidValueInClearingAccount => decide
  | invalidUseOfTradingCollarDollarValue => decide
  | invalidForCurrentSymbolTradingStatusOrMarketState => decide
  | primaryExchangeIpoNotCompleteIpoInProgress => decide
  | invalidUseOfMinQtySizeOrMinQtyExecTypeInstruction => decide
  | invalidUseOfOrderType => decide
  | invalidMaxFloorQty => decide
  | invalidDisplayRangeQty => decide
  | featureNotAvailable => decide
  | primaryListingMarketRoutingNotSupported => decide
  | tooLateForPrimaryListingMarketOrder => decide
  | pacOrdersAreNotAllowedRoutingToPrimary => decide
  | shortSaleExemptOrdersNotAllowed => decide
  | limitPriceMoreAggressiveThanMarketImpactCollar => decide
  | marketOrdersNotAllowed => decide
  | restrictedSecurityNotAllowed => decide
  | blockedByOrderRateMetrics => decide
  | averageDailyVolumeProtection => decide
  | invalidOffsetForPrimaryPegOrder => decide
  | invalidPurgeGroupSpecified => decide
  | invalidOrNotPermittedValueInLocateAccount => decide
  | blockedByDropCopyAcodEvent => decide
  | blockedByDropCopyAcosfEvent => decide
  | invalidUseOfCancelOrderIfNotANbboSetter => decide
  | invalidOrderExpiryTime => decide
  | earlyTradingSessionRestriction => decide
  | lateTradingSessionRestriction => decide
  | downgradedFromOlderVersion => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : OrderStatus) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (OrderStatus × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : OrderStatus) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : OrderStatus) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end OrderStatus

/-- Modify Status: one byte code -/
def ModifyStatus.codes : List UInt8 :=
  [0x20, 0x41, 0x42, 0x43, 0x44, 0x45, 0x46, 0x47, 0x48, 0x49, 0x4A, 0x4B, 0x4C, 0x4D, 0x4E, 0x4F, 0x50, 0x51, 0x52, 0x53, 0x54, 0x55, 0x56, 0x57, 0x58, 0x5A, 0x61, 0x62, 0x63, 0x64, 0x70, 0x74, 0x79, 0x7A, 0x30, 0x31, 0x32, 0x33, 0x34, 0x37, 0x38, 0x39, 0x40, 0x23, 0x24, 0x2A]

inductive ModifyStatus where
  | successful -- Successful
  | duplicateClientOrderId -- Duplicate Client Order Id
  | notInLiveOrderWindow -- Not In Live Order Window
  | matchingEngineIsNotAvailable -- Matching Engine Is Not Available
  | cannotFindOrderWithTargetClientOrderId -- Cannot Find Order With Target Client Order Id
  | exceededTestSymbolThrottle -- Exceeded Test Symbol Throttle
  | orderIsRouted -- Order Is Routed
  | shortSaleOrdersNotAllowed -- Short Sale Orders Not Allowed
  | blockedByMeoUser -- Blocked By Meo User
  | invalidMpid -- Invalid Mpid
  | invalidPrice -- Invalid Price
  | invalidSize -- Invalid Size
  | blockedByFirmOverMiaxMemberFirmPortalOrByHelpdesk -- Blocked By Firm Over Miax Member Firm Portal Or By Helpdesk
  | exceededMaxAllowedSize -- Exceeded Max Allowed Size
  | exceededMaxNotionalValue -- Exceeded Max Notional Value
  | invalidClientOrderId -- Invalid Client Order Id
  | requestIsNotPermittedForThisSession -- Request Is Not Permitted For This Session
  | specifiedMpidDoesNotMatchTargetOrder -- Specified Mpid Does Not Match Target Order
  | blockedByCumulativeRiskMetrics -- Blocked By Cumulative Risk Metrics
  | invalidSymbolId -- Invalid Symbol Id
  | invalidTargetClientOrderId -- Invalid Target Client Order Id
  | invalidUseOfLocateRequired -- Invalid Use Of Locate Required
  | invalidSellShort -- Invalid Sell Short
  | limitOrderPriceProtection -- Limit Order Price Protection
  | mpidNotPermitted -- Mpid Not Permitted
  | undefinedReason -- Undefined Reason
  | invalidMinQtyModification -- Invalid Min Qty Modification
  | invalidToChangeMaxFloorQty -- Invalid To Change Max Floor Qty
  | modificationRequestIsSentToAnotherMarketAndPendingCompletion -- Modification Request Is Sent To Another Market And Pending Completion
  | notAllowedOrderIsAlreadyPendingModification -- Not Allowed Order Is Already Pending Modification
  | invalidForCurrentSymbolTradingStatusOrMarketState -- Invalid For Current Symbol Trading Status Or Market State
  | invalidMaxFloorQty -- Invalid Max Floor Qty
  | pacOrdersAreNotAllowedRoutingToPrimary -- Pac Orders Are Not Allowed Routing To Primary
  | shortSaleExemptOrdersNotAllowed -- Short Sale Exempt Orders Not Allowed
  | limitPriceMoreAggressiveThanMarketImpact -- Limit Price More Aggressive Than Market Impact
  | marketOrdersNotAllowed -- Market Orders Not Allowed
  | restrictedSecurityNotAllowed -- Restricted Security Not Allowed
  | blockedByOrderRateMetrics -- Blocked By Order Rate Metrics
  | averageDailyVolumeProtection -- Average Daily Volume Protection
  | invalidOrNotPermittedValueInLocateAccountField -- Invalid Or Not Permitted Value In Locate Account Field
  | blockedByDropCopyAcodEvent -- Blocked By Drop Copy Acod Event
  | blockedByDropCopyAcosfEvent -- Blocked By Drop Copy Acosf Event
  | invalidOrderExpiryTime -- Invalid Order Expiry Time
  | earlyTradingSessionRestriction -- Early Trading Session Restriction
  | lateTradingSessionRestriction -- Late Trading Session Restriction
  | downgradedFromOlderVersion -- Downgraded From Older Version
  | unlisted (byte : { byte : UInt8 // byte ∉ ModifyStatus.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ModifyStatus

def toByte : ModifyStatus → UInt8
  | .successful => 0x20
  | .duplicateClientOrderId => 0x41
  | .notInLiveOrderWindow => 0x42
  | .matchingEngineIsNotAvailable => 0x43
  | .cannotFindOrderWithTargetClientOrderId => 0x44
  | .exceededTestSymbolThrottle => 0x45
  | .orderIsRouted => 0x46
  | .shortSaleOrdersNotAllowed => 0x47
  | .blockedByMeoUser => 0x48
  | .invalidMpid => 0x49
  | .invalidPrice => 0x4A
  | .invalidSize => 0x4B
  | .blockedByFirmOverMiaxMemberFirmPortalOrByHelpdesk => 0x4C
  | .exceededMaxAllowedSize => 0x4D
  | .exceededMaxNotionalValue => 0x4E
  | .invalidClientOrderId => 0x4F
  | .requestIsNotPermittedForThisSession => 0x50
  | .specifiedMpidDoesNotMatchTargetOrder => 0x51
  | .blockedByCumulativeRiskMetrics => 0x52
  | .invalidSymbolId => 0x53
  | .invalidTargetClientOrderId => 0x54
  | .invalidUseOfLocateRequired => 0x55
  | .invalidSellShort => 0x56
  | .limitOrderPriceProtection => 0x57
  | .mpidNotPermitted => 0x58
  | .undefinedReason => 0x5A
  | .invalidMinQtyModification => 0x61
  | .invalidToChangeMaxFloorQty => 0x62
  | .modificationRequestIsSentToAnotherMarketAndPendingCompletion => 0x63
  | .notAllowedOrderIsAlreadyPendingModification => 0x64
  | .invalidForCurrentSymbolTradingStatusOrMarketState => 0x70
  | .invalidMaxFloorQty => 0x74
  | .pacOrdersAreNotAllowedRoutingToPrimary => 0x79
  | .shortSaleExemptOrdersNotAllowed => 0x7A
  | .limitPriceMoreAggressiveThanMarketImpact => 0x30
  | .marketOrdersNotAllowed => 0x31
  | .restrictedSecurityNotAllowed => 0x32
  | .blockedByOrderRateMetrics => 0x33
  | .averageDailyVolumeProtection => 0x34
  | .invalidOrNotPermittedValueInLocateAccountField => 0x37
  | .blockedByDropCopyAcodEvent => 0x38
  | .blockedByDropCopyAcosfEvent => 0x39
  | .invalidOrderExpiryTime => 0x40
  | .earlyTradingSessionRestriction => 0x23
  | .lateTradingSessionRestriction => 0x24
  | .downgradedFromOlderVersion => 0x2A
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ModifyStatus :=
  if byte = 0x20 then .successful
  else if byte = 0x41 then .duplicateClientOrderId
  else if byte = 0x42 then .notInLiveOrderWindow
  else if byte = 0x43 then .matchingEngineIsNotAvailable
  else if byte = 0x44 then .cannotFindOrderWithTargetClientOrderId
  else if byte = 0x45 then .exceededTestSymbolThrottle
  else if byte = 0x46 then .orderIsRouted
  else if byte = 0x47 then .shortSaleOrdersNotAllowed
  else if byte = 0x48 then .blockedByMeoUser
  else if byte = 0x49 then .invalidMpid
  else if byte = 0x4A then .invalidPrice
  else if byte = 0x4B then .invalidSize
  else if byte = 0x4C then .blockedByFirmOverMiaxMemberFirmPortalOrByHelpdesk
  else if byte = 0x4D then .exceededMaxAllowedSize
  else if byte = 0x4E then .exceededMaxNotionalValue
  else if byte = 0x4F then .invalidClientOrderId
  else if byte = 0x50 then .requestIsNotPermittedForThisSession
  else if byte = 0x51 then .specifiedMpidDoesNotMatchTargetOrder
  else if byte = 0x52 then .blockedByCumulativeRiskMetrics
  else if byte = 0x53 then .invalidSymbolId
  else if byte = 0x54 then .invalidTargetClientOrderId
  else if byte = 0x55 then .invalidUseOfLocateRequired
  else if byte = 0x56 then .invalidSellShort
  else if byte = 0x57 then .limitOrderPriceProtection
  else if byte = 0x58 then .mpidNotPermitted
  else if byte = 0x5A then .undefinedReason
  else if byte = 0x61 then .invalidMinQtyModification
  else if byte = 0x62 then .invalidToChangeMaxFloorQty
  else if byte = 0x63 then .modificationRequestIsSentToAnotherMarketAndPendingCompletion
  else if byte = 0x64 then .notAllowedOrderIsAlreadyPendingModification
  else if byte = 0x70 then .invalidForCurrentSymbolTradingStatusOrMarketState
  else if byte = 0x74 then .invalidMaxFloorQty
  else if byte = 0x79 then .pacOrdersAreNotAllowedRoutingToPrimary
  else if byte = 0x7A then .shortSaleExemptOrdersNotAllowed
  else if byte = 0x30 then .limitPriceMoreAggressiveThanMarketImpact
  else if byte = 0x31 then .marketOrdersNotAllowed
  else if byte = 0x32 then .restrictedSecurityNotAllowed
  else if byte = 0x33 then .blockedByOrderRateMetrics
  else if byte = 0x34 then .averageDailyVolumeProtection
  else if byte = 0x37 then .invalidOrNotPermittedValueInLocateAccountField
  else if byte = 0x38 then .blockedByDropCopyAcodEvent
  else if byte = 0x39 then .blockedByDropCopyAcosfEvent
  else if byte = 0x40 then .invalidOrderExpiryTime
  else if byte = 0x23 then .earlyTradingSessionRestriction
  else if byte = 0x24 then .lateTradingSessionRestriction
  else .downgradedFromOlderVersion

def ofByte (byte : UInt8) : ModifyStatus :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ModifyStatus) : ofByte value.toByte = value := by
  cases value with
  | successful => decide
  | duplicateClientOrderId => decide
  | notInLiveOrderWindow => decide
  | matchingEngineIsNotAvailable => decide
  | cannotFindOrderWithTargetClientOrderId => decide
  | exceededTestSymbolThrottle => decide
  | orderIsRouted => decide
  | shortSaleOrdersNotAllowed => decide
  | blockedByMeoUser => decide
  | invalidMpid => decide
  | invalidPrice => decide
  | invalidSize => decide
  | blockedByFirmOverMiaxMemberFirmPortalOrByHelpdesk => decide
  | exceededMaxAllowedSize => decide
  | exceededMaxNotionalValue => decide
  | invalidClientOrderId => decide
  | requestIsNotPermittedForThisSession => decide
  | specifiedMpidDoesNotMatchTargetOrder => decide
  | blockedByCumulativeRiskMetrics => decide
  | invalidSymbolId => decide
  | invalidTargetClientOrderId => decide
  | invalidUseOfLocateRequired => decide
  | invalidSellShort => decide
  | limitOrderPriceProtection => decide
  | mpidNotPermitted => decide
  | undefinedReason => decide
  | invalidMinQtyModification => decide
  | invalidToChangeMaxFloorQty => decide
  | modificationRequestIsSentToAnotherMarketAndPendingCompletion => decide
  | notAllowedOrderIsAlreadyPendingModification => decide
  | invalidForCurrentSymbolTradingStatusOrMarketState => decide
  | invalidMaxFloorQty => decide
  | pacOrdersAreNotAllowedRoutingToPrimary => decide
  | shortSaleExemptOrdersNotAllowed => decide
  | limitPriceMoreAggressiveThanMarketImpact => decide
  | marketOrdersNotAllowed => decide
  | restrictedSecurityNotAllowed => decide
  | blockedByOrderRateMetrics => decide
  | averageDailyVolumeProtection => decide
  | invalidOrNotPermittedValueInLocateAccountField => decide
  | blockedByDropCopyAcodEvent => decide
  | blockedByDropCopyAcosfEvent => decide
  | invalidOrderExpiryTime => decide
  | earlyTradingSessionRestriction => decide
  | lateTradingSessionRestriction => decide
  | downgradedFromOlderVersion => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ModifyStatus) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ModifyStatus × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ModifyStatus) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : ModifyStatus) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ModifyStatus

/-- Cancel Status: one byte code -/
def CancelStatus.codes : List UInt8 :=
  [0x20, 0x41, 0x42, 0x43, 0x44, 0x45, 0x46, 0x49, 0x4F, 0x50, 0x51, 0x53, 0x54, 0x58, 0x5A, 0x63, 0x2A]

inductive CancelStatus where
  | successful -- Successful
  | duplicateClientOrderId -- Duplicate Client Order Id
  | notInLiveOrderWindow -- Not In Live Order Window
  | matchingEngineIsNotAvailable -- Matching Engine Is Not Available
  | cannotFindOrderWithTargetClientOrderId -- Cannot Find Order With Target Client Order Id
  | exceededTestSymbolThrottle -- Exceeded Test Symbol Throttle
  | orderIsRouted -- Order Is Routed
  | invalidMpid -- Invalid Mpid
  | invalidClientOrderId -- Invalid Client Order Id
  | requestIsNotPermittedForThisSession -- Request Is Not Permitted For This Session
  | specifiedMpidDoesNotMatchTargetOrder -- Specified Mpid Does Not Match Target Order
  | invalidSymbolId -- Invalid Symbol Id
  | invalidTargetClientOrderId -- Invalid Target Client Order Id
  | mpidNotPermitted -- Mpid Not Permitted
  | undefinedReason -- Undefined Reason
  | modificationRequestIsSentToAnotherMarketAndPendingCompletion -- Modification Request Is Sent To Another Market And Pending Completion
  | downgradedFromOlderVersion -- Downgraded From Older Version
  | unlisted (byte : { byte : UInt8 // byte ∉ CancelStatus.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace CancelStatus

def toByte : CancelStatus → UInt8
  | .successful => 0x20
  | .duplicateClientOrderId => 0x41
  | .notInLiveOrderWindow => 0x42
  | .matchingEngineIsNotAvailable => 0x43
  | .cannotFindOrderWithTargetClientOrderId => 0x44
  | .exceededTestSymbolThrottle => 0x45
  | .orderIsRouted => 0x46
  | .invalidMpid => 0x49
  | .invalidClientOrderId => 0x4F
  | .requestIsNotPermittedForThisSession => 0x50
  | .specifiedMpidDoesNotMatchTargetOrder => 0x51
  | .invalidSymbolId => 0x53
  | .invalidTargetClientOrderId => 0x54
  | .mpidNotPermitted => 0x58
  | .undefinedReason => 0x5A
  | .modificationRequestIsSentToAnotherMarketAndPendingCompletion => 0x63
  | .downgradedFromOlderVersion => 0x2A
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : CancelStatus :=
  if byte = 0x20 then .successful
  else if byte = 0x41 then .duplicateClientOrderId
  else if byte = 0x42 then .notInLiveOrderWindow
  else if byte = 0x43 then .matchingEngineIsNotAvailable
  else if byte = 0x44 then .cannotFindOrderWithTargetClientOrderId
  else if byte = 0x45 then .exceededTestSymbolThrottle
  else if byte = 0x46 then .orderIsRouted
  else if byte = 0x49 then .invalidMpid
  else if byte = 0x4F then .invalidClientOrderId
  else if byte = 0x50 then .requestIsNotPermittedForThisSession
  else if byte = 0x51 then .specifiedMpidDoesNotMatchTargetOrder
  else if byte = 0x53 then .invalidSymbolId
  else if byte = 0x54 then .invalidTargetClientOrderId
  else if byte = 0x58 then .mpidNotPermitted
  else if byte = 0x5A then .undefinedReason
  else if byte = 0x63 then .modificationRequestIsSentToAnotherMarketAndPendingCompletion
  else .downgradedFromOlderVersion

def ofByte (byte : UInt8) : CancelStatus :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : CancelStatus) : ofByte value.toByte = value := by
  cases value with
  | successful => decide
  | duplicateClientOrderId => decide
  | notInLiveOrderWindow => decide
  | matchingEngineIsNotAvailable => decide
  | cannotFindOrderWithTargetClientOrderId => decide
  | exceededTestSymbolThrottle => decide
  | orderIsRouted => decide
  | invalidMpid => decide
  | invalidClientOrderId => decide
  | requestIsNotPermittedForThisSession => decide
  | specifiedMpidDoesNotMatchTargetOrder => decide
  | invalidSymbolId => decide
  | invalidTargetClientOrderId => decide
  | mpidNotPermitted => decide
  | undefinedReason => decide
  | modificationRequestIsSentToAnotherMarketAndPendingCompletion => decide
  | downgradedFromOlderVersion => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : CancelStatus) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (CancelStatus × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : CancelStatus) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : CancelStatus) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end CancelStatus

/-- System Status: one byte code -/
def SystemStatus.codes : List UInt8 :=
  [0x53, 0x43, 0x31, 0x32]

inductive SystemStatus where
  | startOfSystemHours -- Start Of System Hours
  | endOfSystemHours -- End Of System Hours
  | startOfTestSession -- Start Of Test Session
  | endOfTestSession -- End Of Test Session
  | unlisted (byte : { byte : UInt8 // byte ∉ SystemStatus.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace SystemStatus

def toByte : SystemStatus → UInt8
  | .startOfSystemHours => 0x53
  | .endOfSystemHours => 0x43
  | .startOfTestSession => 0x31
  | .endOfTestSession => 0x32
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : SystemStatus :=
  if byte = 0x53 then .startOfSystemHours
  else if byte = 0x43 then .endOfSystemHours
  else if byte = 0x31 then .startOfTestSession
  else .endOfTestSession

def ofByte (byte : UInt8) : SystemStatus :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : SystemStatus) : ofByte value.toByte = value := by
  cases value with
  | startOfSystemHours => decide
  | endOfSystemHours => decide
  | startOfTestSession => decide
  | endOfTestSession => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : SystemStatus) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (SystemStatus × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : SystemStatus) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : SystemStatus) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end SystemStatus

/-- Time In Force: one byte code -/
def TimeInForce.codes : List UInt8 :=
  [0x52, 0x49, 0x44, 0x46, 0x54, 0x45]

inductive TimeInForce where
  | regularHoursOnly -- Regular Hours Only
  | immediateOrCancel -- Immediate Or Cancel
  | regularHoursOnly_44 -- Regular Hours Only
  | fillOrKill -- Fill Or Kill
  | goodUntilTime -- Good Until Time
  | goodUntilExtendedDay -- Good Until Extended Day
  | unlisted (byte : { byte : UInt8 // byte ∉ TimeInForce.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TimeInForce

def toByte : TimeInForce → UInt8
  | .regularHoursOnly => 0x52
  | .immediateOrCancel => 0x49
  | .regularHoursOnly_44 => 0x44
  | .fillOrKill => 0x46
  | .goodUntilTime => 0x54
  | .goodUntilExtendedDay => 0x45
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TimeInForce :=
  if byte = 0x52 then .regularHoursOnly
  else if byte = 0x49 then .immediateOrCancel
  else if byte = 0x44 then .regularHoursOnly_44
  else if byte = 0x46 then .fillOrKill
  else if byte = 0x54 then .goodUntilTime
  else .goodUntilExtendedDay

def ofByte (byte : UInt8) : TimeInForce :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TimeInForce) : ofByte value.toByte = value := by
  cases value with
  | regularHoursOnly => decide
  | immediateOrCancel => decide
  | regularHoursOnly_44 => decide
  | fillOrKill => decide
  | goodUntilTime => decide
  | goodUntilExtendedDay => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : TimeInForce) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (TimeInForce × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : TimeInForce) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : TimeInForce) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end TimeInForce

/-- Order Type: one byte code -/
def OrderType.codes : List UInt8 :=
  [0x31, 0x32, 0x4D, 0x6D, 0x52, 0x72]

inductive OrderType where
  | limit -- Limit
  | market -- Market
  | midpointPeg -- Midpoint Peg
  | midpointPegButDoNotMatchWhenNbboIsLocked -- Midpoint Peg But Do Not Match When Nbbo Is Locked
  | primaryPeg -- Primary Peg
  | primaryPegButDoNotMatchWhenNbboIsLocked -- Primary Peg But Do Not Match When Nbbo Is Locked
  | unlisted (byte : { byte : UInt8 // byte ∉ OrderType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OrderType

def toByte : OrderType → UInt8
  | .limit => 0x31
  | .market => 0x32
  | .midpointPeg => 0x4D
  | .midpointPegButDoNotMatchWhenNbboIsLocked => 0x6D
  | .primaryPeg => 0x52
  | .primaryPegButDoNotMatchWhenNbboIsLocked => 0x72
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OrderType :=
  if byte = 0x31 then .limit
  else if byte = 0x32 then .market
  else if byte = 0x4D then .midpointPeg
  else if byte = 0x6D then .midpointPegButDoNotMatchWhenNbboIsLocked
  else if byte = 0x52 then .primaryPeg
  else .primaryPegButDoNotMatchWhenNbboIsLocked

def ofByte (byte : UInt8) : OrderType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OrderType) : ofByte value.toByte = value := by
  cases value with
  | limit => decide
  | market => decide
  | midpointPeg => decide
  | midpointPegButDoNotMatchWhenNbboIsLocked => decide
  | primaryPeg => decide
  | primaryPegButDoNotMatchWhenNbboIsLocked => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : OrderType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (OrderType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : OrderType) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : OrderType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end OrderType

/-- Price Sliding And Reprice Frequency: one byte code -/
def PriceSlidingAndRepriceFrequency.codes : List UInt8 :=
  [0x44, 0x43, 0x4D, 0x4E, 0x51]

inductive PriceSlidingAndRepriceFrequency where
  | repriceOnce -- Reprice Once
  | repriceOnceButCancelIfCrossedAtEntry -- Reprice Once But Cancel If Crossed At Entry
  | repriceMultipleTimes -- Reprice Multiple Times
  | noPriceSliding -- No Price Sliding
  | notApplicable -- Not Applicable
  | unlisted (byte : { byte : UInt8 // byte ∉ PriceSlidingAndRepriceFrequency.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace PriceSlidingAndRepriceFrequency

def toByte : PriceSlidingAndRepriceFrequency → UInt8
  | .repriceOnce => 0x44
  | .repriceOnceButCancelIfCrossedAtEntry => 0x43
  | .repriceMultipleTimes => 0x4D
  | .noPriceSliding => 0x4E
  | .notApplicable => 0x51
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : PriceSlidingAndRepriceFrequency :=
  if byte = 0x44 then .repriceOnce
  else if byte = 0x43 then .repriceOnceButCancelIfCrossedAtEntry
  else if byte = 0x4D then .repriceMultipleTimes
  else if byte = 0x4E then .noPriceSliding
  else .notApplicable

def ofByte (byte : UInt8) : PriceSlidingAndRepriceFrequency :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : PriceSlidingAndRepriceFrequency) : ofByte value.toByte = value := by
  cases value with
  | repriceOnce => decide
  | repriceOnceButCancelIfCrossedAtEntry => decide
  | repriceMultipleTimes => decide
  | noPriceSliding => decide
  | notApplicable => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : PriceSlidingAndRepriceFrequency) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (PriceSlidingAndRepriceFrequency × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : PriceSlidingAndRepriceFrequency) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : PriceSlidingAndRepriceFrequency) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end PriceSlidingAndRepriceFrequency

/-- Capacity: one byte code -/
def Capacity.codes : List UInt8 :=
  [0x41, 0x50, 0x52]

inductive Capacity where
  | agency -- Agency
  | principal -- Principal
  | risklessPrincipal -- Riskless Principal
  | unlisted (byte : { byte : UInt8 // byte ∉ Capacity.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Capacity

def toByte : Capacity → UInt8
  | .agency => 0x41
  | .principal => 0x50
  | .risklessPrincipal => 0x52
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Capacity :=
  if byte = 0x41 then .agency
  else if byte = 0x50 then .principal
  else .risklessPrincipal

def ofByte (byte : UInt8) : Capacity :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Capacity) : ofByte value.toByte = value := by
  cases value with
  | agency => decide
  | principal => decide
  | risklessPrincipal => decide
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

/-- Original Order Capacity: one byte code -/
def OriginalOrderCapacity.codes : List UInt8 :=
  [0x41, 0x50, 0x52]

inductive OriginalOrderCapacity where
  | agency -- Agency
  | principal -- Principal
  | risklessPrincipal -- Riskless Principal
  | unlisted (byte : { byte : UInt8 // byte ∉ OriginalOrderCapacity.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OriginalOrderCapacity

def toByte : OriginalOrderCapacity → UInt8
  | .agency => 0x41
  | .principal => 0x50
  | .risklessPrincipal => 0x52
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OriginalOrderCapacity :=
  if byte = 0x41 then .agency
  else if byte = 0x50 then .principal
  else .risklessPrincipal

def ofByte (byte : UInt8) : OriginalOrderCapacity :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OriginalOrderCapacity) : ofByte value.toByte = value := by
  cases value with
  | agency => decide
  | principal => decide
  | risklessPrincipal => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : OriginalOrderCapacity) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (OriginalOrderCapacity × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : OriginalOrderCapacity) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : OriginalOrderCapacity) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end OriginalOrderCapacity

/-- Pending Modify Status: one byte code -/
def PendingModifyStatus.codes : List UInt8 :=
  [0x20, 0x50, 0x58]

inductive PendingModifyStatus where
  | pendingModificationIsCompletedOr -- Pending Modification Is Completed Or
  | modificationRequestIsSentToAnother -- Modification Request Is Sent To Another
  | pendingModificationRequestIsRejected -- Pending Modification Request Is Rejected
  | unlisted (byte : { byte : UInt8 // byte ∉ PendingModifyStatus.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace PendingModifyStatus

def toByte : PendingModifyStatus → UInt8
  | .pendingModificationIsCompletedOr => 0x20
  | .modificationRequestIsSentToAnother => 0x50
  | .pendingModificationRequestIsRejected => 0x58
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : PendingModifyStatus :=
  if byte = 0x20 then .pendingModificationIsCompletedOr
  else if byte = 0x50 then .modificationRequestIsSentToAnother
  else .pendingModificationRequestIsRejected

def ofByte (byte : UInt8) : PendingModifyStatus :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : PendingModifyStatus) : ofByte value.toByte = value := by
  cases value with
  | pendingModificationIsCompletedOr => decide
  | modificationRequestIsSentToAnother => decide
  | pendingModificationRequestIsRejected => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : PendingModifyStatus) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (PendingModifyStatus × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : PendingModifyStatus) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : PendingModifyStatus) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end PendingModifyStatus

/-- Pending Reject Reason: one byte code -/
def PendingRejectReason.codes : List UInt8 :=
  [0x20, 0x58]

inductive PendingRejectReason where
  | notApplicable -- Not Applicable
  | rejectedByPrimaryListingMarket -- Rejected By Primary Listing Market
  | unlisted (byte : { byte : UInt8 // byte ∉ PendingRejectReason.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace PendingRejectReason

def toByte : PendingRejectReason → UInt8
  | .notApplicable => 0x20
  | .rejectedByPrimaryListingMarket => 0x58
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : PendingRejectReason :=
  if byte = 0x20 then .notApplicable
  else .rejectedByPrimaryListingMarket

def ofByte (byte : UInt8) : PendingRejectReason :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : PendingRejectReason) : ofByte value.toByte = value := by
  cases value with
  | notApplicable => decide
  | rejectedByPrimaryListingMarket => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : PendingRejectReason) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (PendingRejectReason × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : PendingRejectReason) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : PendingRejectReason) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end PendingRejectReason

/-- Cancel Reason: one byte code -/
def CancelReason.codes : List UInt8 :=
  [0x41, 0x42, 0x43, 0x44, 0x45, 0x46, 0x47, 0x48, 0x49, 0x4A, 0x4B, 0x4C, 0x4D, 0x4E, 0x4F, 0x50, 0x51, 0x52, 0x53, 0x54, 0x55, 0x56, 0x57, 0x58, 0x59, 0x30, 0x31, 0x32, 0x33, 0x34, 0x35, 0x36, 0x37, 0x38, 0x5A, 0x2A]

inductive CancelReason where
  | cancelledDueToCumulativeRiskMetrics -- Cancelled Due To Cumulative Risk Metrics
  | reservedForFutureUse -- Reserved For Future Use
  | timeInForceCancelled -- Time In Force Cancelled
  | autoCancelOnDisconnectAcod -- Auto Cancel On Disconnect Acod
  | postOnlyOrderIsLockingcrossingMiax -- Post Only Order Is Lockingcrossing Miax
  | autoCancelOnSystemFailureAcosf -- Auto Cancel On System Failure Acosf
  | cancelledDueToPriceSlidingInstruction -- Cancelled Due To Price Sliding Instruction
  | cancelledByHelpdeskOrOverMiaxMember -- Cancelled By Helpdesk Or Over Miax Member
  | orderExpired -- Order Expired
  | symbolTradingStatusMakesPacMarket -- Symbol Trading Status Makes Pac Market
  | tradingCollarProtection -- Trading Collar Protection
  | sellShortIsoWhenShortSalePriceTestIs -- Sell Short Iso When Short Sale Price Test Is
  | symbolIsNotTrading -- Symbol Is Not Trading
  | limitOrderPriceProtection -- Limit Order Price Protection
  | routeToPrimaryListingMarketRejected -- Route To Primary Listing Market Rejected
  | cancelledByAMassCancelRequestOverAPriorityPurgePort -- Cancelled By A Mass Cancel Request Over A Priority Purge Port
  | unexpectedCancelByPrimaryListingMarket -- Unexpected Cancel By Primary Listing Market
  | cancelledDueToFailedPriceImprovement -- Cancelled Due To Failed Price Improvement
  | cancelledDueToPrimaryAuctionRoute -- Cancelled Due To Primary Auction Route
  | cancelledDueToOrderRateProtection -- Cancelled Due To Order Rate Protection
  | cancelledByUserThroughOrderEntrySession -- Cancelled By User Through Order Entry Session
  | invalidPeggedOrderPrice -- Invalid Pegged Order Price
  | pacOrderCancelledAsSecurityIsHalted -- Pac Order Cancelled As Security Is Halted
  | notApplicableUsedWhenPendingCancel -- Not Applicable Used When Pending Cancel
  | primaryAuctionOrderIsCancelledDueToA -- Primary Auction Order Is Cancelled Due To A
  | cancelledDueToMarketImpactCollar -- Cancelled Due To Market Impact Collar
  | cancelNewestInstruction -- Cancel Newest Instruction
  | cancelOldestInstruction -- Cancel Oldest Instruction
  | cancelBothInstruction -- Cancel Both Instruction
  | decrementAndCancelInstruction -- Decrement And Cancel Instruction
  | cancelledDueToDropCopyAcodEvent -- Cancelled Due To Drop Copy Acod Event
  | cancelledDueToDropCopyAcosfEvent -- Cancelled Due To Drop Copy Acosf Event
  | cancelledAsOrderDidNotSetNbbo -- Cancelled As Order Did Not Set Nbbo
  | cancelledByUserThroughASessionOther -- Cancelled By User Through A Session Other
  | undefinedReason -- Undefined Reason
  | downgradedFromOlderVersion -- Downgraded From Older Version
  | unlisted (byte : { byte : UInt8 // byte ∉ CancelReason.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace CancelReason

def toByte : CancelReason → UInt8
  | .cancelledDueToCumulativeRiskMetrics => 0x41
  | .reservedForFutureUse => 0x42
  | .timeInForceCancelled => 0x43
  | .autoCancelOnDisconnectAcod => 0x44
  | .postOnlyOrderIsLockingcrossingMiax => 0x45
  | .autoCancelOnSystemFailureAcosf => 0x46
  | .cancelledDueToPriceSlidingInstruction => 0x47
  | .cancelledByHelpdeskOrOverMiaxMember => 0x48
  | .orderExpired => 0x49
  | .symbolTradingStatusMakesPacMarket => 0x4A
  | .tradingCollarProtection => 0x4B
  | .sellShortIsoWhenShortSalePriceTestIs => 0x4C
  | .symbolIsNotTrading => 0x4D
  | .limitOrderPriceProtection => 0x4E
  | .routeToPrimaryListingMarketRejected => 0x4F
  | .cancelledByAMassCancelRequestOverAPriorityPurgePort => 0x50
  | .unexpectedCancelByPrimaryListingMarket => 0x51
  | .cancelledDueToFailedPriceImprovement => 0x52
  | .cancelledDueToPrimaryAuctionRoute => 0x53
  | .cancelledDueToOrderRateProtection => 0x54
  | .cancelledByUserThroughOrderEntrySession => 0x55
  | .invalidPeggedOrderPrice => 0x56
  | .pacOrderCancelledAsSecurityIsHalted => 0x57
  | .notApplicableUsedWhenPendingCancel => 0x58
  | .primaryAuctionOrderIsCancelledDueToA => 0x59
  | .cancelledDueToMarketImpactCollar => 0x30
  | .cancelNewestInstruction => 0x31
  | .cancelOldestInstruction => 0x32
  | .cancelBothInstruction => 0x33
  | .decrementAndCancelInstruction => 0x34
  | .cancelledDueToDropCopyAcodEvent => 0x35
  | .cancelledDueToDropCopyAcosfEvent => 0x36
  | .cancelledAsOrderDidNotSetNbbo => 0x37
  | .cancelledByUserThroughASessionOther => 0x38
  | .undefinedReason => 0x5A
  | .downgradedFromOlderVersion => 0x2A
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : CancelReason :=
  if byte = 0x41 then .cancelledDueToCumulativeRiskMetrics
  else if byte = 0x42 then .reservedForFutureUse
  else if byte = 0x43 then .timeInForceCancelled
  else if byte = 0x44 then .autoCancelOnDisconnectAcod
  else if byte = 0x45 then .postOnlyOrderIsLockingcrossingMiax
  else if byte = 0x46 then .autoCancelOnSystemFailureAcosf
  else if byte = 0x47 then .cancelledDueToPriceSlidingInstruction
  else if byte = 0x48 then .cancelledByHelpdeskOrOverMiaxMember
  else if byte = 0x49 then .orderExpired
  else if byte = 0x4A then .symbolTradingStatusMakesPacMarket
  else if byte = 0x4B then .tradingCollarProtection
  else if byte = 0x4C then .sellShortIsoWhenShortSalePriceTestIs
  else if byte = 0x4D then .symbolIsNotTrading
  else if byte = 0x4E then .limitOrderPriceProtection
  else if byte = 0x4F then .routeToPrimaryListingMarketRejected
  else if byte = 0x50 then .cancelledByAMassCancelRequestOverAPriorityPurgePort
  else if byte = 0x51 then .unexpectedCancelByPrimaryListingMarket
  else if byte = 0x52 then .cancelledDueToFailedPriceImprovement
  else if byte = 0x53 then .cancelledDueToPrimaryAuctionRoute
  else if byte = 0x54 then .cancelledDueToOrderRateProtection
  else if byte = 0x55 then .cancelledByUserThroughOrderEntrySession
  else if byte = 0x56 then .invalidPeggedOrderPrice
  else if byte = 0x57 then .pacOrderCancelledAsSecurityIsHalted
  else if byte = 0x58 then .notApplicableUsedWhenPendingCancel
  else if byte = 0x59 then .primaryAuctionOrderIsCancelledDueToA
  else if byte = 0x30 then .cancelledDueToMarketImpactCollar
  else if byte = 0x31 then .cancelNewestInstruction
  else if byte = 0x32 then .cancelOldestInstruction
  else if byte = 0x33 then .cancelBothInstruction
  else if byte = 0x34 then .decrementAndCancelInstruction
  else if byte = 0x35 then .cancelledDueToDropCopyAcodEvent
  else if byte = 0x36 then .cancelledDueToDropCopyAcosfEvent
  else if byte = 0x37 then .cancelledAsOrderDidNotSetNbbo
  else if byte = 0x38 then .cancelledByUserThroughASessionOther
  else if byte = 0x5A then .undefinedReason
  else .downgradedFromOlderVersion

def ofByte (byte : UInt8) : CancelReason :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : CancelReason) : ofByte value.toByte = value := by
  cases value with
  | cancelledDueToCumulativeRiskMetrics => decide
  | reservedForFutureUse => decide
  | timeInForceCancelled => decide
  | autoCancelOnDisconnectAcod => decide
  | postOnlyOrderIsLockingcrossingMiax => decide
  | autoCancelOnSystemFailureAcosf => decide
  | cancelledDueToPriceSlidingInstruction => decide
  | cancelledByHelpdeskOrOverMiaxMember => decide
  | orderExpired => decide
  | symbolTradingStatusMakesPacMarket => decide
  | tradingCollarProtection => decide
  | sellShortIsoWhenShortSalePriceTestIs => decide
  | symbolIsNotTrading => decide
  | limitOrderPriceProtection => decide
  | routeToPrimaryListingMarketRejected => decide
  | cancelledByAMassCancelRequestOverAPriorityPurgePort => decide
  | unexpectedCancelByPrimaryListingMarket => decide
  | cancelledDueToFailedPriceImprovement => decide
  | cancelledDueToPrimaryAuctionRoute => decide
  | cancelledDueToOrderRateProtection => decide
  | cancelledByUserThroughOrderEntrySession => decide
  | invalidPeggedOrderPrice => decide
  | pacOrderCancelledAsSecurityIsHalted => decide
  | notApplicableUsedWhenPendingCancel => decide
  | primaryAuctionOrderIsCancelledDueToA => decide
  | cancelledDueToMarketImpactCollar => decide
  | cancelNewestInstruction => decide
  | cancelOldestInstruction => decide
  | cancelBothInstruction => decide
  | decrementAndCancelInstruction => decide
  | cancelledDueToDropCopyAcodEvent => decide
  | cancelledDueToDropCopyAcosfEvent => decide
  | cancelledAsOrderDidNotSetNbbo => decide
  | cancelledByUserThroughASessionOther => decide
  | undefinedReason => decide
  | downgradedFromOlderVersion => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : CancelReason) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (CancelReason × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : CancelReason) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : CancelReason) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end CancelReason

/-- Pending Cancel Status: one byte code -/
def PendingCancelStatus.codes : List UInt8 :=
  [0x20, 0x58, 0x50]

inductive PendingCancelStatus where
  | completedOrNotApplicable -- Completed Or Not Applicable
  | pendingCancellationRequestIsRejected -- Pending Cancellation Request Is Rejected
  | cancelRequestWasReceivedButIsPending -- Cancel Request Was Received But Is Pending
  | unlisted (byte : { byte : UInt8 // byte ∉ PendingCancelStatus.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace PendingCancelStatus

def toByte : PendingCancelStatus → UInt8
  | .completedOrNotApplicable => 0x20
  | .pendingCancellationRequestIsRejected => 0x58
  | .cancelRequestWasReceivedButIsPending => 0x50
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : PendingCancelStatus :=
  if byte = 0x20 then .completedOrNotApplicable
  else if byte = 0x58 then .pendingCancellationRequestIsRejected
  else .cancelRequestWasReceivedButIsPending

def ofByte (byte : UInt8) : PendingCancelStatus :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : PendingCancelStatus) : ofByte value.toByte = value := by
  cases value with
  | completedOrNotApplicable => decide
  | pendingCancellationRequestIsRejected => decide
  | cancelRequestWasReceivedButIsPending => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : PendingCancelStatus) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (PendingCancelStatus × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : PendingCancelStatus) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : PendingCancelStatus) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end PendingCancelStatus

/-- Nbbo Indicator: one byte code -/
def NbboIndicator.codes : List UInt8 :=
  [0x59, 0x46, 0x53, 0x4A, 0x4E]

inductive NbboIndicator where
  | nbboSetter -- Nbbo Setter
  | nbboFirstJoiner -- Nbbo First Joiner
  | nbboSetterWithSize -- Nbbo Setter With Size
  | nbboFirstJoinerWithSize -- Nbbo First Joiner With Size
  | notApplicable -- Not Applicable
  | unlisted (byte : { byte : UInt8 // byte ∉ NbboIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace NbboIndicator

def toByte : NbboIndicator → UInt8
  | .nbboSetter => 0x59
  | .nbboFirstJoiner => 0x46
  | .nbboSetterWithSize => 0x53
  | .nbboFirstJoinerWithSize => 0x4A
  | .notApplicable => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : NbboIndicator :=
  if byte = 0x59 then .nbboSetter
  else if byte = 0x46 then .nbboFirstJoiner
  else if byte = 0x53 then .nbboSetterWithSize
  else if byte = 0x4A then .nbboFirstJoinerWithSize
  else .notApplicable

def ofByte (byte : UInt8) : NbboIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : NbboIndicator) : ofByte value.toByte = value := by
  cases value with
  | nbboSetter => decide
  | nbboFirstJoiner => decide
  | nbboSetterWithSize => decide
  | nbboFirstJoinerWithSize => decide
  | notApplicable => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : NbboIndicator) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (NbboIndicator × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : NbboIndicator) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : NbboIndicator) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end NbboIndicator

/-- Trade Status: one byte code -/
def TradeStatus.codes : List UInt8 :=
  [0x45, 0x43, 0x58]

inductive TradeStatus where
  | newExecution -- New Execution
  | priceSizeCorrection -- Price Size Correction
  | tradeCancellation -- Trade Cancellation
  | unlisted (byte : { byte : UInt8 // byte ∉ TradeStatus.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TradeStatus

def toByte : TradeStatus → UInt8
  | .newExecution => 0x45
  | .priceSizeCorrection => 0x43
  | .tradeCancellation => 0x58
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TradeStatus :=
  if byte = 0x45 then .newExecution
  else if byte = 0x43 then .priceSizeCorrection
  else .tradeCancellation

def ofByte (byte : UInt8) : TradeStatus :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TradeStatus) : ofByte value.toByte = value := by
  cases value with
  | newExecution => decide
  | priceSizeCorrection => decide
  | tradeCancellation => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : TradeStatus) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (TradeStatus × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : TradeStatus) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : TradeStatus) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end TradeStatus

/-- Executing Trading Center: one byte code -/
def ExecutingTradingCenter.codes : List UInt8 :=
  [0x41, 0x42, 0x43, 0x48, 0x49, 0x4A, 0x4B, 0x4C, 0x4D, 0x4E, 0x50, 0x51, 0x55, 0x56, 0x58, 0x59, 0x5A]

inductive ExecutingTradingCenter where
  | nyseAmerican -- Nyse American
  | nasdaqBx -- Nasdaq Bx
  | nyseNational -- Nyse National
  | miaxPearlEquities -- Miax Pearl Equities
  | nasdaqIse -- Nasdaq Ise
  | cboeEdgaExchange -- Cboe Edga Exchange
  | cboeEdgxExchange -- Cboe Edgx Exchange
  | longTermStockExchange -- Long Term Stock Exchange
  | nyseChicago -- Nyse Chicago
  | newYorkStockExchange -- New York Stock Exchange
  | nyseArca -- Nyse Arca
  | nasdaq -- Nasdaq
  | membersExchange -- Members Exchange
  | investorsExchange -- Investors Exchange
  | nasdaqPhlx -- Nasdaq Phlx
  | cboeByxExchange -- Cboe Byx Exchange
  | cboeBzxExchange -- Cboe Bzx Exchange
  | unlisted (byte : { byte : UInt8 // byte ∉ ExecutingTradingCenter.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ExecutingTradingCenter

def toByte : ExecutingTradingCenter → UInt8
  | .nyseAmerican => 0x41
  | .nasdaqBx => 0x42
  | .nyseNational => 0x43
  | .miaxPearlEquities => 0x48
  | .nasdaqIse => 0x49
  | .cboeEdgaExchange => 0x4A
  | .cboeEdgxExchange => 0x4B
  | .longTermStockExchange => 0x4C
  | .nyseChicago => 0x4D
  | .newYorkStockExchange => 0x4E
  | .nyseArca => 0x50
  | .nasdaq => 0x51
  | .membersExchange => 0x55
  | .investorsExchange => 0x56
  | .nasdaqPhlx => 0x58
  | .cboeByxExchange => 0x59
  | .cboeBzxExchange => 0x5A
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ExecutingTradingCenter :=
  if byte = 0x41 then .nyseAmerican
  else if byte = 0x42 then .nasdaqBx
  else if byte = 0x43 then .nyseNational
  else if byte = 0x48 then .miaxPearlEquities
  else if byte = 0x49 then .nasdaqIse
  else if byte = 0x4A then .cboeEdgaExchange
  else if byte = 0x4B then .cboeEdgxExchange
  else if byte = 0x4C then .longTermStockExchange
  else if byte = 0x4D then .nyseChicago
  else if byte = 0x4E then .newYorkStockExchange
  else if byte = 0x50 then .nyseArca
  else if byte = 0x51 then .nasdaq
  else if byte = 0x55 then .membersExchange
  else if byte = 0x56 then .investorsExchange
  else if byte = 0x58 then .nasdaqPhlx
  else if byte = 0x59 then .cboeByxExchange
  else .cboeBzxExchange

def ofByte (byte : UInt8) : ExecutingTradingCenter :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ExecutingTradingCenter) : ofByte value.toByte = value := by
  cases value with
  | nyseAmerican => decide
  | nasdaqBx => decide
  | nyseNational => decide
  | miaxPearlEquities => decide
  | nasdaqIse => decide
  | cboeEdgaExchange => decide
  | cboeEdgxExchange => decide
  | longTermStockExchange => decide
  | nyseChicago => decide
  | newYorkStockExchange => decide
  | nyseArca => decide
  | nasdaq => decide
  | membersExchange => decide
  | investorsExchange => decide
  | nasdaqPhlx => decide
  | cboeByxExchange => decide
  | cboeBzxExchange => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ExecutingTradingCenter) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ExecutingTradingCenter × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ExecutingTradingCenter) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : ExecutingTradingCenter) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ExecutingTradingCenter

/-- Scope: one byte code -/
def Scope.codes : List UInt8 :=
  [0x4D]

inductive Scope where
  | purgeAllOrdersForSpecifiedMpid -- Purge All Orders For Specified Mpid
  | unlisted (byte : { byte : UInt8 // byte ∉ Scope.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Scope

def toByte : Scope → UInt8
  | .purgeAllOrdersForSpecifiedMpid => 0x4D
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (_ : UInt8) : Scope :=
  .purgeAllOrdersForSpecifiedMpid

def ofByte (byte : UInt8) : Scope :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Scope) : ofByte value.toByte = value := by
  cases value with
  | purgeAllOrdersForSpecifiedMpid => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Scope) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Scope × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Scope) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : Scope) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Scope

/-- Action: one byte code -/
def Action.codes : List UInt8 :=
  [0x42, 0x4D, 0x58, 0x52]

inductive Action where
  | blockOnly -- Block Only
  | massCancelOnly -- Mass Cancel Only
  | blockAndMassCancel -- Block And Mass Cancel
  | removeBlockingForTheSpecifiedScope -- Remove Blocking For The Specified Scope
  | unlisted (byte : { byte : UInt8 // byte ∉ Action.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Action

def toByte : Action → UInt8
  | .blockOnly => 0x42
  | .massCancelOnly => 0x4D
  | .blockAndMassCancel => 0x58
  | .removeBlockingForTheSpecifiedScope => 0x52
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Action :=
  if byte = 0x42 then .blockOnly
  else if byte = 0x4D then .massCancelOnly
  else if byte = 0x58 then .blockAndMassCancel
  else .removeBlockingForTheSpecifiedScope

def ofByte (byte : UInt8) : Action :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Action) : ofByte value.toByte = value := by
  cases value with
  | blockOnly => decide
  | massCancelOnly => decide
  | blockAndMassCancel => decide
  | removeBlockingForTheSpecifiedScope => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Action) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Action × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Action) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : Action) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Action

/-- Purge Status: one byte code -/
def PurgeStatus.codes : List UInt8 :=
  [0x20, 0x43, 0x45, 0x49, 0x4A, 0x4F, 0x50, 0x53, 0x58, 0x5A, 0x2A]

inductive PurgeStatus where
  | successful -- Successful
  | matchingEngineIsNotAvailable -- Matching Engine Is Not Available
  | exceededTestSymbolThrottle -- Exceeded Test Symbol Throttle
  | invalidMpid -- Invalid Mpid
  | invalidPrice -- Invalid Price
  | invalidClientOrderId -- Invalid Client Order Id
  | requestIsNotPermittedForThisSession -- Request Is Not Permitted For This Session
  | invalidSymbolId -- Invalid Symbol Id
  | mpidNotPermitted -- Mpid Not Permitted
  | undefinedReason -- Undefined Reason
  | downgradedFromOlderVersion -- Downgraded From Older Version
  | unlisted (byte : { byte : UInt8 // byte ∉ PurgeStatus.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace PurgeStatus

def toByte : PurgeStatus → UInt8
  | .successful => 0x20
  | .matchingEngineIsNotAvailable => 0x43
  | .exceededTestSymbolThrottle => 0x45
  | .invalidMpid => 0x49
  | .invalidPrice => 0x4A
  | .invalidClientOrderId => 0x4F
  | .requestIsNotPermittedForThisSession => 0x50
  | .invalidSymbolId => 0x53
  | .mpidNotPermitted => 0x58
  | .undefinedReason => 0x5A
  | .downgradedFromOlderVersion => 0x2A
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : PurgeStatus :=
  if byte = 0x20 then .successful
  else if byte = 0x43 then .matchingEngineIsNotAvailable
  else if byte = 0x45 then .exceededTestSymbolThrottle
  else if byte = 0x49 then .invalidMpid
  else if byte = 0x4A then .invalidPrice
  else if byte = 0x4F then .invalidClientOrderId
  else if byte = 0x50 then .requestIsNotPermittedForThisSession
  else if byte = 0x53 then .invalidSymbolId
  else if byte = 0x58 then .mpidNotPermitted
  else if byte = 0x5A then .undefinedReason
  else .downgradedFromOlderVersion

def ofByte (byte : UInt8) : PurgeStatus :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : PurgeStatus) : ofByte value.toByte = value := by
  cases value with
  | successful => decide
  | matchingEngineIsNotAvailable => decide
  | exceededTestSymbolThrottle => decide
  | invalidMpid => decide
  | invalidPrice => decide
  | invalidClientOrderId => decide
  | requestIsNotPermittedForThisSession => decide
  | invalidSymbolId => decide
  | mpidNotPermitted => decide
  | undefinedReason => decide
  | downgradedFromOlderVersion => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : PurgeStatus) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (PurgeStatus × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : PurgeStatus) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : PurgeStatus) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end PurgeStatus

/-- Login Status: one byte code -/
def LoginStatus.codes : List UInt8 :=
  [0x20, 0x53, 0x55, 0x58, 0x4E, 0x49, 0x41, 0x4C]

inductive LoginStatus where
  | successful -- Successful
  | invalidTradingSessionRequested -- Invalid Trading Session Requested
  | noActiveTradingSessionExists -- No Active Trading Session Exists
  | rejected -- Rejected
  | invalidStartSequenceNumberRequested -- Invalid Start Sequence Number Requested
  | incompatibleSessionProtocolVersion -- Incompatible Session Protocol Version
  | incompatibleApplicationProtocolVersion -- Incompatible Application Protocol Version
  | requestRejectedBecauseClientAlreadyLoggedIn -- Request Rejected Because Client Already Logged In
  | unlisted (byte : { byte : UInt8 // byte ∉ LoginStatus.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace LoginStatus

def toByte : LoginStatus → UInt8
  | .successful => 0x20
  | .invalidTradingSessionRequested => 0x53
  | .noActiveTradingSessionExists => 0x55
  | .rejected => 0x58
  | .invalidStartSequenceNumberRequested => 0x4E
  | .incompatibleSessionProtocolVersion => 0x49
  | .incompatibleApplicationProtocolVersion => 0x41
  | .requestRejectedBecauseClientAlreadyLoggedIn => 0x4C
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : LoginStatus :=
  if byte = 0x20 then .successful
  else if byte = 0x53 then .invalidTradingSessionRequested
  else if byte = 0x55 then .noActiveTradingSessionExists
  else if byte = 0x58 then .rejected
  else if byte = 0x4E then .invalidStartSequenceNumberRequested
  else if byte = 0x49 then .incompatibleSessionProtocolVersion
  else if byte = 0x41 then .incompatibleApplicationProtocolVersion
  else .requestRejectedBecauseClientAlreadyLoggedIn

def ofByte (byte : UInt8) : LoginStatus :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : LoginStatus) : ofByte value.toByte = value := by
  cases value with
  | successful => decide
  | invalidTradingSessionRequested => decide
  | noActiveTradingSessionExists => decide
  | rejected => decide
  | invalidStartSequenceNumberRequested => decide
  | incompatibleSessionProtocolVersion => decide
  | incompatibleApplicationProtocolVersion => decide
  | requestRejectedBecauseClientAlreadyLoggedIn => decide
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

/-- Logout Reason: one byte code -/
def LogoutReason.codes : List UInt8 :=
  [0x20, 0x42, 0x4C, 0x41]

inductive LogoutReason where
  | gracefulLogout -- Graceful Logout
  | badPacket -- Bad Packet
  | timedOut -- Timed Out
  | applicationTerminatingConnection -- Application Terminating Connection
  | unlisted (byte : { byte : UInt8 // byte ∉ LogoutReason.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace LogoutReason

def toByte : LogoutReason → UInt8
  | .gracefulLogout => 0x20
  | .badPacket => 0x42
  | .timedOut => 0x4C
  | .applicationTerminatingConnection => 0x41
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : LogoutReason :=
  if byte = 0x20 then .gracefulLogout
  else if byte = 0x42 then .badPacket
  else if byte = 0x4C then .timedOut
  else .applicationTerminatingConnection

def ofByte (byte : UInt8) : LogoutReason :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : LogoutReason) : ofByte value.toByte = value := by
  cases value with
  | gracefulLogout => decide
  | badPacket => decide
  | timedOut => decide
  | applicationTerminatingConnection => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : LogoutReason) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (LogoutReason × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : LogoutReason) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : LogoutReason) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end LogoutReason

/-- Symbol Update: 59 bytes -/
structure SymbolUpdate where
  matchingEngineTime : BitVec 64
  symbolId : BitVec 32
  tickerSymbol : Alpha 11
  reserved1 : Alpha 1
  testSecurityIndicator : TestSecurityIndicator
  future : BitVec 8
  lotSize : BitVec 32
  openingTime : Alpha 8
  closingTime : Alpha 8
  primaryMarketCode : PrimaryMarketCode
  reserved12 : Alpha 12
  deriving DecidableEq, Repr

namespace SymbolUpdate

def encode (message : SymbolUpdate) : List UInt8 :=
  encodeUIntLE 8 message.matchingEngineTime
    ++ (encodeUIntLE 4 message.symbolId
    ++ (Alpha.encode message.tickerSymbol
    ++ (Alpha.encode message.reserved1
    ++ (TestSecurityIndicator.encode message.testSecurityIndicator
    ++ (encodeUIntLE 1 message.future
    ++ (encodeUIntLE 4 message.lotSize
    ++ (Alpha.encode message.openingTime
    ++ (Alpha.encode message.closingTime
    ++ (PrimaryMarketCode.encode message.primaryMarketCode
    ++ (Alpha.encode message.reserved12))))))))))

def decode (bytes : List UInt8) : Option (SymbolUpdate × List UInt8) := do
  let (matchingEngineTime, bytes) ← decodeUIntLE 8 bytes
  let (symbolId, bytes) ← decodeUIntLE 4 bytes
  let (tickerSymbol, bytes) ← Alpha.decode 11 bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  let (testSecurityIndicator, bytes) ← TestSecurityIndicator.decode bytes
  let (future, bytes) ← decodeUIntLE 1 bytes
  let (lotSize, bytes) ← decodeUIntLE 4 bytes
  let (openingTime, bytes) ← Alpha.decode 8 bytes
  let (closingTime, bytes) ← Alpha.decode 8 bytes
  let (primaryMarketCode, bytes) ← PrimaryMarketCode.decode bytes
  let (reserved12, bytes) ← Alpha.decode 12 bytes
  pure ({ matchingEngineTime, symbolId, tickerSymbol, reserved1, testSecurityIndicator, future, lotSize, openingTime, closingTime, primaryMarketCode, reserved12 }, bytes)

@[simp] theorem encode_length (message : SymbolUpdate) : (encode message).length = 59 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, TestSecurityIndicator.encode_length, PrimaryMarketCode.encode_length]

theorem encode_length_pos (message : SymbolUpdate) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SymbolUpdate) (rest : List UInt8) :
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
  rw [List.append_assoc, TestSecurityIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, PrimaryMarketCode.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end SymbolUpdate

/-- New Order Response Message: 76 bytes -/
structure NewOrderResponseMessage where
  matchingEngineTime : BitVec 64
  mpid : Alpha 4
  clientOrderId : Alpha 20
  symbolId : BitVec 32
  orderId : BitVec 64
  price : BitVec 64
  size : BitVec 32
  orderStatus : OrderStatus
  reserved19 : Alpha 19
  deriving DecidableEq, Repr

namespace NewOrderResponseMessage

def encode (message : NewOrderResponseMessage) : List UInt8 :=
  encodeUIntLE 8 message.matchingEngineTime
    ++ (Alpha.encode message.mpid
    ++ (Alpha.encode message.clientOrderId
    ++ (encodeUIntLE 4 message.symbolId
    ++ (encodeUIntLE 8 message.orderId
    ++ (encodeUIntLE 8 message.price
    ++ (encodeUIntLE 4 message.size
    ++ (OrderStatus.encode message.orderStatus
    ++ (Alpha.encode message.reserved19))))))))

def decode (bytes : List UInt8) : Option (NewOrderResponseMessage × List UInt8) := do
  let (matchingEngineTime, bytes) ← decodeUIntLE 8 bytes
  let (mpid, bytes) ← Alpha.decode 4 bytes
  let (clientOrderId, bytes) ← Alpha.decode 20 bytes
  let (symbolId, bytes) ← decodeUIntLE 4 bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (size, bytes) ← decodeUIntLE 4 bytes
  let (orderStatus, bytes) ← OrderStatus.decode bytes
  let (reserved19, bytes) ← Alpha.decode 19 bytes
  pure ({ matchingEngineTime, mpid, clientOrderId, symbolId, orderId, price, size, orderStatus, reserved19 }, bytes)

@[simp] theorem encode_length (message : NewOrderResponseMessage) : (encode message).length = 76 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, OrderStatus.encode_length]

theorem encode_length_pos (message : NewOrderResponseMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : NewOrderResponseMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, OrderStatus.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end NewOrderResponseMessage

/-- Modify Order Response: 87 bytes -/
structure ModifyOrderResponse where
  matchingEngineTime : BitVec 64
  mpid : Alpha 4
  clientOrderId : Alpha 20
  originalClientOrderId : Alpha 20
  symbolId : BitVec 32
  orderId : BitVec 64
  leavesQty : BitVec 32
  price : BitVec 64
  modifyStatus : ModifyStatus
  reserved10 : Alpha 10
  deriving DecidableEq, Repr

namespace ModifyOrderResponse

def encode (message : ModifyOrderResponse) : List UInt8 :=
  encodeUIntLE 8 message.matchingEngineTime
    ++ (Alpha.encode message.mpid
    ++ (Alpha.encode message.clientOrderId
    ++ (Alpha.encode message.originalClientOrderId
    ++ (encodeUIntLE 4 message.symbolId
    ++ (encodeUIntLE 8 message.orderId
    ++ (encodeUIntLE 4 message.leavesQty
    ++ (encodeUIntLE 8 message.price
    ++ (ModifyStatus.encode message.modifyStatus
    ++ (Alpha.encode message.reserved10)))))))))

def decode (bytes : List UInt8) : Option (ModifyOrderResponse × List UInt8) := do
  let (matchingEngineTime, bytes) ← decodeUIntLE 8 bytes
  let (mpid, bytes) ← Alpha.decode 4 bytes
  let (clientOrderId, bytes) ← Alpha.decode 20 bytes
  let (originalClientOrderId, bytes) ← Alpha.decode 20 bytes
  let (symbolId, bytes) ← decodeUIntLE 4 bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (leavesQty, bytes) ← decodeUIntLE 4 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (modifyStatus, bytes) ← ModifyStatus.decode bytes
  let (reserved10, bytes) ← Alpha.decode 10 bytes
  pure ({ matchingEngineTime, mpid, clientOrderId, originalClientOrderId, symbolId, orderId, leavesQty, price, modifyStatus, reserved10 }, bytes)

@[simp] theorem encode_length (message : ModifyOrderResponse) : (encode message).length = 87 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, ModifyStatus.encode_length]

theorem encode_length_pos (message : ModifyOrderResponse) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ModifyOrderResponse) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, ModifyStatus.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end ModifyOrderResponse

/-- Cancel Order Response: 79 bytes -/
structure CancelOrderResponse where
  matchingEngineTime : BitVec 64
  mpid : Alpha 4
  clientOrderId : Alpha 20
  originalClientOrderId : Alpha 20
  symbolId : BitVec 32
  orderId : BitVec 64
  leavesQty : BitVec 32
  cancelStatus : CancelStatus
  reserved10 : Alpha 10
  deriving DecidableEq, Repr

namespace CancelOrderResponse

def encode (message : CancelOrderResponse) : List UInt8 :=
  encodeUIntLE 8 message.matchingEngineTime
    ++ (Alpha.encode message.mpid
    ++ (Alpha.encode message.clientOrderId
    ++ (Alpha.encode message.originalClientOrderId
    ++ (encodeUIntLE 4 message.symbolId
    ++ (encodeUIntLE 8 message.orderId
    ++ (encodeUIntLE 4 message.leavesQty
    ++ (CancelStatus.encode message.cancelStatus
    ++ (Alpha.encode message.reserved10))))))))

def decode (bytes : List UInt8) : Option (CancelOrderResponse × List UInt8) := do
  let (matchingEngineTime, bytes) ← decodeUIntLE 8 bytes
  let (mpid, bytes) ← Alpha.decode 4 bytes
  let (clientOrderId, bytes) ← Alpha.decode 20 bytes
  let (originalClientOrderId, bytes) ← Alpha.decode 20 bytes
  let (symbolId, bytes) ← decodeUIntLE 4 bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (leavesQty, bytes) ← decodeUIntLE 4 bytes
  let (cancelStatus, bytes) ← CancelStatus.decode bytes
  let (reserved10, bytes) ← Alpha.decode 10 bytes
  pure ({ matchingEngineTime, mpid, clientOrderId, originalClientOrderId, symbolId, orderId, leavesQty, cancelStatus, reserved10 }, bytes)

@[simp] theorem encode_length (message : CancelOrderResponse) : (encode message).length = 79 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, CancelStatus.encode_length]

theorem encode_length_pos (message : CancelOrderResponse) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CancelOrderResponse) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, CancelStatus.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end CancelOrderResponse

/-- Cancel Order By Exchange Order Id Response Message: 59 bytes -/
structure CancelOrderByExchangeOrderIdResponseMessage where
  matchingEngineTime : BitVec 64
  mpid : Alpha 4
  clientOrderId : Alpha 20
  symbolId : BitVec 32
  orderId : BitVec 64
  leavesQty : BitVec 32
  cancelStatus : CancelStatus
  reserved10 : Alpha 10
  deriving DecidableEq, Repr

namespace CancelOrderByExchangeOrderIdResponseMessage

def encode (message : CancelOrderByExchangeOrderIdResponseMessage) : List UInt8 :=
  encodeUIntLE 8 message.matchingEngineTime
    ++ (Alpha.encode message.mpid
    ++ (Alpha.encode message.clientOrderId
    ++ (encodeUIntLE 4 message.symbolId
    ++ (encodeUIntLE 8 message.orderId
    ++ (encodeUIntLE 4 message.leavesQty
    ++ (CancelStatus.encode message.cancelStatus
    ++ (Alpha.encode message.reserved10)))))))

def decode (bytes : List UInt8) : Option (CancelOrderByExchangeOrderIdResponseMessage × List UInt8) := do
  let (matchingEngineTime, bytes) ← decodeUIntLE 8 bytes
  let (mpid, bytes) ← Alpha.decode 4 bytes
  let (clientOrderId, bytes) ← Alpha.decode 20 bytes
  let (symbolId, bytes) ← decodeUIntLE 4 bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (leavesQty, bytes) ← decodeUIntLE 4 bytes
  let (cancelStatus, bytes) ← CancelStatus.decode bytes
  let (reserved10, bytes) ← Alpha.decode 10 bytes
  pure ({ matchingEngineTime, mpid, clientOrderId, symbolId, orderId, leavesQty, cancelStatus, reserved10 }, bytes)

@[simp] theorem encode_length (message : CancelOrderByExchangeOrderIdResponseMessage) : (encode message).length = 59 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, CancelStatus.encode_length]

theorem encode_length_pos (message : CancelOrderByExchangeOrderIdResponseMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CancelOrderByExchangeOrderIdResponseMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, CancelStatus.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end CancelOrderByExchangeOrderIdResponseMessage

/-- System State Notification: 26 bytes -/
structure SystemStateNotification where
  matchingEngineTime : BitVec 64
  meoVersion : Alpha 8
  sessionId : BitVec 8
  systemStatus : SystemStatus
  reserved8 : Alpha 8
  deriving DecidableEq, Repr

namespace SystemStateNotification

def encode (message : SystemStateNotification) : List UInt8 :=
  encodeUIntLE 8 message.matchingEngineTime
    ++ (Alpha.encode message.meoVersion
    ++ (encodeUIntLE 1 message.sessionId
    ++ (SystemStatus.encode message.systemStatus
    ++ (Alpha.encode message.reserved8))))

def decode (bytes : List UInt8) : Option (SystemStateNotification × List UInt8) := do
  let (matchingEngineTime, bytes) ← decodeUIntLE 8 bytes
  let (meoVersion, bytes) ← Alpha.decode 8 bytes
  let (sessionId, bytes) ← decodeUIntLE 1 bytes
  let (systemStatus, bytes) ← SystemStatus.decode bytes
  let (reserved8, bytes) ← Alpha.decode 8 bytes
  pure ({ matchingEngineTime, meoVersion, sessionId, systemStatus, reserved8 }, bytes)

@[simp] theorem encode_length (message : SystemStateNotification) : (encode message).length = 26 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, SystemStatus.encode_length]

theorem encode_length_pos (message : SystemStateNotification) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SystemStateNotification) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, SystemStatus.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end SystemStateNotification

/-- New Order Notification: 137 bytes -/
structure NewOrderNotification where
  matchingEngineTime : BitVec 64
  mpid : Alpha 4
  orderId : BitVec 64
  clientOrderId : Alpha 20
  symbolId : BitVec 32
  price : BitVec 64
  size : BitVec 32
  newOrderInstructions : BitVec 16
  timeInForce : TimeInForce
  orderType : OrderType
  priceSlidingAndRepriceFrequency : PriceSlidingAndRepriceFrequency
  selfTradeProtection : BitVec 8
  selfTradeProtectionGroup : Alpha 1
  routing : BitVec 8
  tradingCollarDollarValue : BitVec 64
  capacity : Capacity
  account : Alpha 16
  clearingAccount : Alpha 4
  minQty : BitVec 32
  maxFloorQty : BitVec 32
  displayRangeQty : BitVec 32
  pegOffset : BitVec 64
  locateAccount : Alpha 4
  purgeGroup : Alpha 1
  originalOrderCapacity : OriginalOrderCapacity
  orderExpiryTime : BitVec 64
  reserved10 : Alpha 10
  deriving DecidableEq, Repr

namespace NewOrderNotification

def encode (message : NewOrderNotification) : List UInt8 :=
  encodeUIntLE 8 message.matchingEngineTime
    ++ (Alpha.encode message.mpid
    ++ (encodeUIntLE 8 message.orderId
    ++ (Alpha.encode message.clientOrderId
    ++ (encodeUIntLE 4 message.symbolId
    ++ (encodeUIntLE 8 message.price
    ++ (encodeUIntLE 4 message.size
    ++ (encodeUIntLE 2 message.newOrderInstructions
    ++ (TimeInForce.encode message.timeInForce
    ++ (OrderType.encode message.orderType
    ++ (PriceSlidingAndRepriceFrequency.encode message.priceSlidingAndRepriceFrequency
    ++ (encodeUIntLE 1 message.selfTradeProtection
    ++ (Alpha.encode message.selfTradeProtectionGroup
    ++ (encodeUIntLE 1 message.routing
    ++ (encodeUIntLE 8 message.tradingCollarDollarValue
    ++ (Capacity.encode message.capacity
    ++ (Alpha.encode message.account
    ++ (Alpha.encode message.clearingAccount
    ++ (encodeUIntLE 4 message.minQty
    ++ (encodeUIntLE 4 message.maxFloorQty
    ++ (encodeUIntLE 4 message.displayRangeQty
    ++ (encodeUIntLE 8 message.pegOffset
    ++ (Alpha.encode message.locateAccount
    ++ (Alpha.encode message.purgeGroup
    ++ (OriginalOrderCapacity.encode message.originalOrderCapacity
    ++ (encodeUIntLE 8 message.orderExpiryTime
    ++ (Alpha.encode message.reserved10))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (NewOrderNotification × List UInt8) := do
  let (matchingEngineTime, bytes) ← decodeUIntLE 8 bytes
  let (mpid, bytes) ← Alpha.decode 4 bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (clientOrderId, bytes) ← Alpha.decode 20 bytes
  let (symbolId, bytes) ← decodeUIntLE 4 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (size, bytes) ← decodeUIntLE 4 bytes
  let (newOrderInstructions, bytes) ← decodeUIntLE 2 bytes
  let (timeInForce, bytes) ← TimeInForce.decode bytes
  let (orderType, bytes) ← OrderType.decode bytes
  let (priceSlidingAndRepriceFrequency, bytes) ← PriceSlidingAndRepriceFrequency.decode bytes
  let (selfTradeProtection, bytes) ← decodeUIntLE 1 bytes
  let (selfTradeProtectionGroup, bytes) ← Alpha.decode 1 bytes
  let (routing, bytes) ← decodeUIntLE 1 bytes
  let (tradingCollarDollarValue, bytes) ← decodeUIntLE 8 bytes
  let (capacity, bytes) ← Capacity.decode bytes
  let (account, bytes) ← Alpha.decode 16 bytes
  let (clearingAccount, bytes) ← Alpha.decode 4 bytes
  let (minQty, bytes) ← decodeUIntLE 4 bytes
  let (maxFloorQty, bytes) ← decodeUIntLE 4 bytes
  let (displayRangeQty, bytes) ← decodeUIntLE 4 bytes
  let (pegOffset, bytes) ← decodeUIntLE 8 bytes
  let (locateAccount, bytes) ← Alpha.decode 4 bytes
  let (purgeGroup, bytes) ← Alpha.decode 1 bytes
  let (originalOrderCapacity, bytes) ← OriginalOrderCapacity.decode bytes
  let (orderExpiryTime, bytes) ← decodeUIntLE 8 bytes
  let (reserved10, bytes) ← Alpha.decode 10 bytes
  pure ({ matchingEngineTime, mpid, orderId, clientOrderId, symbolId, price, size, newOrderInstructions, timeInForce, orderType, priceSlidingAndRepriceFrequency, selfTradeProtection, selfTradeProtectionGroup, routing, tradingCollarDollarValue, capacity, account, clearingAccount, minQty, maxFloorQty, displayRangeQty, pegOffset, locateAccount, purgeGroup, originalOrderCapacity, orderExpiryTime, reserved10 }, bytes)

@[simp] theorem encode_length (message : NewOrderNotification) : (encode message).length = 137 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, TimeInForce.encode_length, OrderType.encode_length, PriceSlidingAndRepriceFrequency.encode_length, Capacity.encode_length, OriginalOrderCapacity.encode_length]

theorem encode_length_pos (message : NewOrderNotification) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : NewOrderNotification) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, TimeInForce.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OrderType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, PriceSlidingAndRepriceFrequency.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Capacity.decode_encode, some_bind]
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OriginalOrderCapacity.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end NewOrderNotification

/-- Modify Order Notification: 121 bytes -/
structure ModifyOrderNotification where
  matchingEngineTime : BitVec 64
  mpid : Alpha 4
  clientOrderId : Alpha 20
  originalClientOrderId : Alpha 20
  symbolId : BitVec 32
  orderId : BitVec 64
  price : BitVec 64
  size : BitVec 32
  leavesQty : BitVec 32
  modifyOrderInstructions : BitVec 8
  minQty : BitVec 32
  maxFloorQty : BitVec 32
  pendingModifyStatus : PendingModifyStatus
  pendingRejectReason : PendingRejectReason
  locateAccount : Alpha 4
  timeInForce : TimeInForce
  orderExpiryTime : BitVec 64
  reserved17 : Alpha 17
  deriving DecidableEq, Repr

namespace ModifyOrderNotification

def encode (message : ModifyOrderNotification) : List UInt8 :=
  encodeUIntLE 8 message.matchingEngineTime
    ++ (Alpha.encode message.mpid
    ++ (Alpha.encode message.clientOrderId
    ++ (Alpha.encode message.originalClientOrderId
    ++ (encodeUIntLE 4 message.symbolId
    ++ (encodeUIntLE 8 message.orderId
    ++ (encodeUIntLE 8 message.price
    ++ (encodeUIntLE 4 message.size
    ++ (encodeUIntLE 4 message.leavesQty
    ++ (encodeUIntLE 1 message.modifyOrderInstructions
    ++ (encodeUIntLE 4 message.minQty
    ++ (encodeUIntLE 4 message.maxFloorQty
    ++ (PendingModifyStatus.encode message.pendingModifyStatus
    ++ (PendingRejectReason.encode message.pendingRejectReason
    ++ (Alpha.encode message.locateAccount
    ++ (TimeInForce.encode message.timeInForce
    ++ (encodeUIntLE 8 message.orderExpiryTime
    ++ (Alpha.encode message.reserved17)))))))))))))))))

def decode (bytes : List UInt8) : Option (ModifyOrderNotification × List UInt8) := do
  let (matchingEngineTime, bytes) ← decodeUIntLE 8 bytes
  let (mpid, bytes) ← Alpha.decode 4 bytes
  let (clientOrderId, bytes) ← Alpha.decode 20 bytes
  let (originalClientOrderId, bytes) ← Alpha.decode 20 bytes
  let (symbolId, bytes) ← decodeUIntLE 4 bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (size, bytes) ← decodeUIntLE 4 bytes
  let (leavesQty, bytes) ← decodeUIntLE 4 bytes
  let (modifyOrderInstructions, bytes) ← decodeUIntLE 1 bytes
  let (minQty, bytes) ← decodeUIntLE 4 bytes
  let (maxFloorQty, bytes) ← decodeUIntLE 4 bytes
  let (pendingModifyStatus, bytes) ← PendingModifyStatus.decode bytes
  let (pendingRejectReason, bytes) ← PendingRejectReason.decode bytes
  let (locateAccount, bytes) ← Alpha.decode 4 bytes
  let (timeInForce, bytes) ← TimeInForce.decode bytes
  let (orderExpiryTime, bytes) ← decodeUIntLE 8 bytes
  let (reserved17, bytes) ← Alpha.decode 17 bytes
  pure ({ matchingEngineTime, mpid, clientOrderId, originalClientOrderId, symbolId, orderId, price, size, leavesQty, modifyOrderInstructions, minQty, maxFloorQty, pendingModifyStatus, pendingRejectReason, locateAccount, timeInForce, orderExpiryTime, reserved17 }, bytes)

@[simp] theorem encode_length (message : ModifyOrderNotification) : (encode message).length = 121 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, PendingModifyStatus.encode_length, PendingRejectReason.encode_length, TimeInForce.encode_length]

theorem encode_length_pos (message : ModifyOrderNotification) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ModifyOrderNotification) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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
  rw [List.append_assoc, PendingModifyStatus.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, PendingRejectReason.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TimeInForce.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end ModifyOrderNotification

/-- Cancel Reduce Size Order Notification: 71 bytes -/
structure CancelReduceSizeOrderNotification where
  matchingEngineTime : BitVec 64
  mpid : Alpha 4
  clientOrderId : Alpha 20
  symbolId : BitVec 32
  orderId : BitVec 64
  leavesQty : BitVec 32
  cancelReason : CancelReason
  lastPrice : BitVec 64
  lastSize : BitVec 32
  pendingCancelStatus : PendingCancelStatus
  pendingRejectReason : PendingRejectReason
  reserved8 : Alpha 8
  deriving DecidableEq, Repr

namespace CancelReduceSizeOrderNotification

def encode (message : CancelReduceSizeOrderNotification) : List UInt8 :=
  encodeUIntLE 8 message.matchingEngineTime
    ++ (Alpha.encode message.mpid
    ++ (Alpha.encode message.clientOrderId
    ++ (encodeUIntLE 4 message.symbolId
    ++ (encodeUIntLE 8 message.orderId
    ++ (encodeUIntLE 4 message.leavesQty
    ++ (CancelReason.encode message.cancelReason
    ++ (encodeUIntLE 8 message.lastPrice
    ++ (encodeUIntLE 4 message.lastSize
    ++ (PendingCancelStatus.encode message.pendingCancelStatus
    ++ (PendingRejectReason.encode message.pendingRejectReason
    ++ (Alpha.encode message.reserved8)))))))))))

def decode (bytes : List UInt8) : Option (CancelReduceSizeOrderNotification × List UInt8) := do
  let (matchingEngineTime, bytes) ← decodeUIntLE 8 bytes
  let (mpid, bytes) ← Alpha.decode 4 bytes
  let (clientOrderId, bytes) ← Alpha.decode 20 bytes
  let (symbolId, bytes) ← decodeUIntLE 4 bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (leavesQty, bytes) ← decodeUIntLE 4 bytes
  let (cancelReason, bytes) ← CancelReason.decode bytes
  let (lastPrice, bytes) ← decodeUIntLE 8 bytes
  let (lastSize, bytes) ← decodeUIntLE 4 bytes
  let (pendingCancelStatus, bytes) ← PendingCancelStatus.decode bytes
  let (pendingRejectReason, bytes) ← PendingRejectReason.decode bytes
  let (reserved8, bytes) ← Alpha.decode 8 bytes
  pure ({ matchingEngineTime, mpid, clientOrderId, symbolId, orderId, leavesQty, cancelReason, lastPrice, lastSize, pendingCancelStatus, pendingRejectReason, reserved8 }, bytes)

@[simp] theorem encode_length (message : CancelReduceSizeOrderNotification) : (encode message).length = 71 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, CancelReason.encode_length, PendingCancelStatus.encode_length, PendingRejectReason.encode_length]

theorem encode_length_pos (message : CancelReduceSizeOrderNotification) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CancelReduceSizeOrderNotification) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, CancelReason.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, PendingCancelStatus.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, PendingRejectReason.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end CancelReduceSizeOrderNotification

/-- Order Price Update Notification: 58 bytes -/
structure OrderPriceUpdateNotification where
  matchingEngineTime : BitVec 64
  symbolId : BitVec 32
  orderId : BitVec 64
  clientOrderId : Alpha 20
  workingPrice : BitVec 64
  nbboIndicator : NbboIndicator
  reserved9 : Alpha 9
  deriving DecidableEq, Repr

namespace OrderPriceUpdateNotification

def encode (message : OrderPriceUpdateNotification) : List UInt8 :=
  encodeUIntLE 8 message.matchingEngineTime
    ++ (encodeUIntLE 4 message.symbolId
    ++ (encodeUIntLE 8 message.orderId
    ++ (Alpha.encode message.clientOrderId
    ++ (encodeUIntLE 8 message.workingPrice
    ++ (NbboIndicator.encode message.nbboIndicator
    ++ (Alpha.encode message.reserved9))))))

def decode (bytes : List UInt8) : Option (OrderPriceUpdateNotification × List UInt8) := do
  let (matchingEngineTime, bytes) ← decodeUIntLE 8 bytes
  let (symbolId, bytes) ← decodeUIntLE 4 bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (clientOrderId, bytes) ← Alpha.decode 20 bytes
  let (workingPrice, bytes) ← decodeUIntLE 8 bytes
  let (nbboIndicator, bytes) ← NbboIndicator.decode bytes
  let (reserved9, bytes) ← Alpha.decode 9 bytes
  pure ({ matchingEngineTime, symbolId, orderId, clientOrderId, workingPrice, nbboIndicator, reserved9 }, bytes)

@[simp] theorem encode_length (message : OrderPriceUpdateNotification) : (encode message).length = 58 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, NbboIndicator.encode_length]

theorem encode_length_pos (message : OrderPriceUpdateNotification) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderPriceUpdateNotification) (rest : List UInt8) :
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
  rw [List.append_assoc, NbboIndicator.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end OrderPriceUpdateNotification

/-- Reserve Order Replenishment Notification: 42 bytes -/
structure ReserveOrderReplenishmentNotification where
  matchingEngineTime : BitVec 64
  symbolId : BitVec 32
  orderId : BitVec 64
  secondaryOrderId : BitVec 64
  displayQty : BitVec 32
  reserved10 : Alpha 10
  deriving DecidableEq, Repr

namespace ReserveOrderReplenishmentNotification

def encode (message : ReserveOrderReplenishmentNotification) : List UInt8 :=
  encodeUIntLE 8 message.matchingEngineTime
    ++ (encodeUIntLE 4 message.symbolId
    ++ (encodeUIntLE 8 message.orderId
    ++ (encodeUIntLE 8 message.secondaryOrderId
    ++ (encodeUIntLE 4 message.displayQty
    ++ (Alpha.encode message.reserved10)))))

def decode (bytes : List UInt8) : Option (ReserveOrderReplenishmentNotification × List UInt8) := do
  let (matchingEngineTime, bytes) ← decodeUIntLE 8 bytes
  let (symbolId, bytes) ← decodeUIntLE 4 bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (secondaryOrderId, bytes) ← decodeUIntLE 8 bytes
  let (displayQty, bytes) ← decodeUIntLE 4 bytes
  let (reserved10, bytes) ← Alpha.decode 10 bytes
  pure ({ matchingEngineTime, symbolId, orderId, secondaryOrderId, displayQty, reserved10 }, bytes)

@[simp] theorem encode_length (message : ReserveOrderReplenishmentNotification) : (encode message).length = 42 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : ReserveOrderReplenishmentNotification) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ReserveOrderReplenishmentNotification) (rest : List UInt8) :
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
  rw [Alpha.decode_encode, some_bind]
  rfl

end ReserveOrderReplenishmentNotification

/-- Execution Notification: 102 bytes -/
structure ExecutionNotification where
  matchingEngineTime : BitVec 64
  mpid : Alpha 4
  symbolId : BitVec 32
  clientOrderId : Alpha 20
  tradeId : BitVec 64
  executionId : BitVec 64
  correctionNumber : BitVec 8
  tradeStatus : TradeStatus
  lastPrice : BitVec 64
  lastSize : BitVec 32
  orderExecutionInstructions : BitVec 16
  executingTradingCenter : ExecutingTradingCenter
  secondaryOrderId : BitVec 64
  liquidityIndicator : Alpha 3
  locateAccount : Alpha 4
  originalOrderCapacity : OriginalOrderCapacity
  additionalLiquidityIndicator : BitVec 8
  executingTradingCenterMpid : Alpha 4
  reserved12 : Alpha 12
  deriving DecidableEq, Repr

namespace ExecutionNotification

def encode (message : ExecutionNotification) : List UInt8 :=
  encodeUIntLE 8 message.matchingEngineTime
    ++ (Alpha.encode message.mpid
    ++ (encodeUIntLE 4 message.symbolId
    ++ (Alpha.encode message.clientOrderId
    ++ (encodeUIntLE 8 message.tradeId
    ++ (encodeUIntLE 8 message.executionId
    ++ (encodeUIntLE 1 message.correctionNumber
    ++ (TradeStatus.encode message.tradeStatus
    ++ (encodeUIntLE 8 message.lastPrice
    ++ (encodeUIntLE 4 message.lastSize
    ++ (encodeUIntLE 2 message.orderExecutionInstructions
    ++ (ExecutingTradingCenter.encode message.executingTradingCenter
    ++ (encodeUIntLE 8 message.secondaryOrderId
    ++ (Alpha.encode message.liquidityIndicator
    ++ (Alpha.encode message.locateAccount
    ++ (OriginalOrderCapacity.encode message.originalOrderCapacity
    ++ (encodeUIntLE 1 message.additionalLiquidityIndicator
    ++ (Alpha.encode message.executingTradingCenterMpid
    ++ (Alpha.encode message.reserved12))))))))))))))))))

def decode (bytes : List UInt8) : Option (ExecutionNotification × List UInt8) := do
  let (matchingEngineTime, bytes) ← decodeUIntLE 8 bytes
  let (mpid, bytes) ← Alpha.decode 4 bytes
  let (symbolId, bytes) ← decodeUIntLE 4 bytes
  let (clientOrderId, bytes) ← Alpha.decode 20 bytes
  let (tradeId, bytes) ← decodeUIntLE 8 bytes
  let (executionId, bytes) ← decodeUIntLE 8 bytes
  let (correctionNumber, bytes) ← decodeUIntLE 1 bytes
  let (tradeStatus, bytes) ← TradeStatus.decode bytes
  let (lastPrice, bytes) ← decodeUIntLE 8 bytes
  let (lastSize, bytes) ← decodeUIntLE 4 bytes
  let (orderExecutionInstructions, bytes) ← decodeUIntLE 2 bytes
  let (executingTradingCenter, bytes) ← ExecutingTradingCenter.decode bytes
  let (secondaryOrderId, bytes) ← decodeUIntLE 8 bytes
  let (liquidityIndicator, bytes) ← Alpha.decode 3 bytes
  let (locateAccount, bytes) ← Alpha.decode 4 bytes
  let (originalOrderCapacity, bytes) ← OriginalOrderCapacity.decode bytes
  let (additionalLiquidityIndicator, bytes) ← decodeUIntLE 1 bytes
  let (executingTradingCenterMpid, bytes) ← Alpha.decode 4 bytes
  let (reserved12, bytes) ← Alpha.decode 12 bytes
  pure ({ matchingEngineTime, mpid, symbolId, clientOrderId, tradeId, executionId, correctionNumber, tradeStatus, lastPrice, lastSize, orderExecutionInstructions, executingTradingCenter, secondaryOrderId, liquidityIndicator, locateAccount, originalOrderCapacity, additionalLiquidityIndicator, executingTradingCenterMpid, reserved12 }, bytes)

@[simp] theorem encode_length (message : ExecutionNotification) : (encode message).length = 102 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, TradeStatus.encode_length, ExecutingTradingCenter.encode_length, OriginalOrderCapacity.encode_length]

theorem encode_length_pos (message : ExecutionNotification) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ExecutionNotification) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, TradeStatus.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, ExecutingTradingCenter.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OriginalOrderCapacity.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end ExecutionNotification

/-- Any Sequenced Message, selected by Sequenced Message Type -/
inductive SequencedMessage where
  | symbolUpdate (message : SymbolUpdate) -- "SU" 0x5355
  | newOrderResponseMessage (message : NewOrderResponseMessage) -- "NR" 0x4E52
  | modifyOrderResponse (message : ModifyOrderResponse) -- "MR" 0x4D52
  | cancelOrderResponse (message : CancelOrderResponse) -- "CR" 0x4352
  | cancelOrderByExchangeOrderIdResponseMessage (message : CancelOrderByExchangeOrderIdResponseMessage) -- "CQ" 0x4351
  | systemStateNotification (message : SystemStateNotification) -- "SN" 0x534E
  | newOrderNotification (message : NewOrderNotification) -- "O1" 0x4F31
  | modifyOrderNotification (message : ModifyOrderNotification) -- "MN" 0x4D4E
  | cancelReduceSizeOrderNotification (message : CancelReduceSizeOrderNotification) -- "XN" 0x584E
  | orderPriceUpdateNotification (message : OrderPriceUpdateNotification) -- "P1" 0x5031
  | reserveOrderReplenishmentNotification (message : ReserveOrderReplenishmentNotification) -- "RA" 0x5241
  | executionNotification (message : ExecutionNotification) -- "E1" 0x4531
  deriving DecidableEq, Repr

namespace SequencedMessage

/-- The Sequenced Message Type each message is sent under -/
def tag : SequencedMessage → BitVec 16
  | .symbolUpdate _ => 21333
  | .newOrderResponseMessage _ => 20050
  | .modifyOrderResponse _ => 19794
  | .cancelOrderResponse _ => 17234
  | .cancelOrderByExchangeOrderIdResponseMessage _ => 17233
  | .systemStateNotification _ => 21326
  | .newOrderNotification _ => 20273
  | .modifyOrderNotification _ => 19790
  | .cancelReduceSizeOrderNotification _ => 22606
  | .orderPriceUpdateNotification _ => 20529
  | .reserveOrderReplenishmentNotification _ => 21057
  | .executionNotification _ => 17713

def encode : SequencedMessage → List UInt8
  | .symbolUpdate message => SymbolUpdate.encode message
  | .newOrderResponseMessage message => NewOrderResponseMessage.encode message
  | .modifyOrderResponse message => ModifyOrderResponse.encode message
  | .cancelOrderResponse message => CancelOrderResponse.encode message
  | .cancelOrderByExchangeOrderIdResponseMessage message => CancelOrderByExchangeOrderIdResponseMessage.encode message
  | .systemStateNotification message => SystemStateNotification.encode message
  | .newOrderNotification message => NewOrderNotification.encode message
  | .modifyOrderNotification message => ModifyOrderNotification.encode message
  | .cancelReduceSizeOrderNotification message => CancelReduceSizeOrderNotification.encode message
  | .orderPriceUpdateNotification message => OrderPriceUpdateNotification.encode message
  | .reserveOrderReplenishmentNotification message => ReserveOrderReplenishmentNotification.encode message
  | .executionNotification message => ExecutionNotification.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : SequencedMessage) : (encode message).length ≤ 137 := by
  cases message with
  | symbolUpdate inner =>
    simp only [encode, SymbolUpdate.encode_length]
    omega
  | newOrderResponseMessage inner =>
    simp only [encode, NewOrderResponseMessage.encode_length]
    omega
  | modifyOrderResponse inner =>
    simp only [encode, ModifyOrderResponse.encode_length]
    omega
  | cancelOrderResponse inner =>
    simp only [encode, CancelOrderResponse.encode_length]
    omega
  | cancelOrderByExchangeOrderIdResponseMessage inner =>
    simp only [encode, CancelOrderByExchangeOrderIdResponseMessage.encode_length]
    omega
  | systemStateNotification inner =>
    simp only [encode, SystemStateNotification.encode_length]
    omega
  | newOrderNotification inner =>
    simp only [encode, NewOrderNotification.encode_length]
    omega
  | modifyOrderNotification inner =>
    simp only [encode, ModifyOrderNotification.encode_length]
    omega
  | cancelReduceSizeOrderNotification inner =>
    simp only [encode, CancelReduceSizeOrderNotification.encode_length]
    omega
  | orderPriceUpdateNotification inner =>
    simp only [encode, OrderPriceUpdateNotification.encode_length]
    omega
  | reserveOrderReplenishmentNotification inner =>
    simp only [encode, ReserveOrderReplenishmentNotification.encode_length]
    omega
  | executionNotification inner =>
    simp only [encode, ExecutionNotification.encode_length]
    omega

def decode (tag : BitVec 16) (bytes : List UInt8) : Option (SequencedMessage × List UInt8) :=
  if tag = 21333 then (SymbolUpdate.decode bytes).map fun (message, rest) => (.symbolUpdate message, rest)
  else if tag = 20050 then (NewOrderResponseMessage.decode bytes).map fun (message, rest) => (.newOrderResponseMessage message, rest)
  else if tag = 19794 then (ModifyOrderResponse.decode bytes).map fun (message, rest) => (.modifyOrderResponse message, rest)
  else if tag = 17234 then (CancelOrderResponse.decode bytes).map fun (message, rest) => (.cancelOrderResponse message, rest)
  else if tag = 17233 then (CancelOrderByExchangeOrderIdResponseMessage.decode bytes).map fun (message, rest) => (.cancelOrderByExchangeOrderIdResponseMessage message, rest)
  else if tag = 21326 then (SystemStateNotification.decode bytes).map fun (message, rest) => (.systemStateNotification message, rest)
  else if tag = 20273 then (NewOrderNotification.decode bytes).map fun (message, rest) => (.newOrderNotification message, rest)
  else if tag = 19790 then (ModifyOrderNotification.decode bytes).map fun (message, rest) => (.modifyOrderNotification message, rest)
  else if tag = 22606 then (CancelReduceSizeOrderNotification.decode bytes).map fun (message, rest) => (.cancelReduceSizeOrderNotification message, rest)
  else if tag = 20529 then (OrderPriceUpdateNotification.decode bytes).map fun (message, rest) => (.orderPriceUpdateNotification message, rest)
  else if tag = 21057 then (ReserveOrderReplenishmentNotification.decode bytes).map fun (message, rest) => (.reserveOrderReplenishmentNotification message, rest)
  else if tag = 17713 then (ExecutionNotification.decode bytes).map fun (message, rest) => (.executionNotification message, rest)
  else none

@[simp] theorem decode_encode (message : SequencedMessage) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end SequencedMessage

/-- Sequenced Data Packet -/
structure SequencedDataPacket where
  sequenceNumber : BitVec 64
  matchingEngineId : BitVec 8
  sequencedMessage : SequencedMessage
  deriving DecidableEq, Repr

namespace SequencedDataPacket

def encode (message : SequencedDataPacket) : List UInt8 :=
  encodeUIntLE 8 message.sequenceNumber
    ++ (encodeUInt 1 message.matchingEngineId
    ++ (encodeUInt 2 (SequencedMessage.tag message.sequencedMessage)
    ++ (SequencedMessage.encode message.sequencedMessage)))

def decode (bytes : List UInt8) : Option (SequencedDataPacket × List UInt8) := do
  let (sequenceNumber, bytes) ← decodeUIntLE 8 bytes
  let (matchingEngineId, bytes) ← decodeUInt 1 bytes
  let (sequencedMessageType, bytes) ← decodeUInt 2 bytes
  let (sequencedMessage, bytes) ← SequencedMessage.decode sequencedMessageType bytes
  pure ({ sequenceNumber, matchingEngineId, sequencedMessage }, bytes)

theorem encode_length_pos (message : SequencedDataPacket) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : SequencedDataPacket) : (encode message).length ≤ 148 := by
  unfold encode
  cases message.sequencedMessage with
  | symbolUpdate inner =>
    simp only [SequencedMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, SymbolUpdate.encode_length]
    omega
  | newOrderResponseMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, NewOrderResponseMessage.encode_length]
    omega
  | modifyOrderResponse inner =>
    simp only [SequencedMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, ModifyOrderResponse.encode_length]
    omega
  | cancelOrderResponse inner =>
    simp only [SequencedMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, CancelOrderResponse.encode_length]
    omega
  | cancelOrderByExchangeOrderIdResponseMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, CancelOrderByExchangeOrderIdResponseMessage.encode_length]
    omega
  | systemStateNotification inner =>
    simp only [SequencedMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, SystemStateNotification.encode_length]
    omega
  | newOrderNotification inner =>
    simp only [SequencedMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, NewOrderNotification.encode_length]
    omega
  | modifyOrderNotification inner =>
    simp only [SequencedMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, ModifyOrderNotification.encode_length]
    omega
  | cancelReduceSizeOrderNotification inner =>
    simp only [SequencedMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, CancelReduceSizeOrderNotification.encode_length]
    omega
  | orderPriceUpdateNotification inner =>
    simp only [SequencedMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, OrderPriceUpdateNotification.encode_length]
    omega
  | reserveOrderReplenishmentNotification inner =>
    simp only [SequencedMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, ReserveOrderReplenishmentNotification.encode_length]
    omega
  | executionNotification inner =>
    simp only [SequencedMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, ExecutionNotification.encode_length]
    omega

@[simp] theorem decode_encode (message : SequencedDataPacket) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [SequencedMessage.decode_encode, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : SequencedDataPacket) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end SequencedDataPacket

/-- New Order Request Message: 129 bytes -/
structure NewOrderRequestMessage where
  reserved8 : Alpha 8
  mpid : Alpha 4
  clientOrderId : Alpha 20
  symbolId : BitVec 32
  price : BitVec 64
  size : BitVec 32
  newOrderInstructions : BitVec 16
  timeInForce : TimeInForce
  orderType : OrderType
  priceSlidingAndRepriceFrequency : PriceSlidingAndRepriceFrequency
  selfTradeProtection : BitVec 8
  selfTradeProtectionGroup : Alpha 1
  routing : BitVec 8
  tradingCollarDollarValue : BitVec 64
  capacity : Capacity
  account : Alpha 16
  clearingAccount : Alpha 4
  minQty : BitVec 32
  maxFloorQty : BitVec 32
  displayRangeQty : BitVec 32
  pegOffset : BitVec 64
  locateAccount : Alpha 4
  purgeGroup : Alpha 1
  orderExpiryTime : BitVec 64
  reserved11 : Alpha 11
  deriving DecidableEq, Repr

namespace NewOrderRequestMessage

def encode (message : NewOrderRequestMessage) : List UInt8 :=
  Alpha.encode message.reserved8
    ++ (Alpha.encode message.mpid
    ++ (Alpha.encode message.clientOrderId
    ++ (encodeUIntLE 4 message.symbolId
    ++ (encodeUIntLE 8 message.price
    ++ (encodeUIntLE 4 message.size
    ++ (encodeUIntLE 2 message.newOrderInstructions
    ++ (TimeInForce.encode message.timeInForce
    ++ (OrderType.encode message.orderType
    ++ (PriceSlidingAndRepriceFrequency.encode message.priceSlidingAndRepriceFrequency
    ++ (encodeUIntLE 1 message.selfTradeProtection
    ++ (Alpha.encode message.selfTradeProtectionGroup
    ++ (encodeUIntLE 1 message.routing
    ++ (encodeUIntLE 8 message.tradingCollarDollarValue
    ++ (Capacity.encode message.capacity
    ++ (Alpha.encode message.account
    ++ (Alpha.encode message.clearingAccount
    ++ (encodeUIntLE 4 message.minQty
    ++ (encodeUIntLE 4 message.maxFloorQty
    ++ (encodeUIntLE 4 message.displayRangeQty
    ++ (encodeUIntLE 8 message.pegOffset
    ++ (Alpha.encode message.locateAccount
    ++ (Alpha.encode message.purgeGroup
    ++ (encodeUIntLE 8 message.orderExpiryTime
    ++ (Alpha.encode message.reserved11))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (NewOrderRequestMessage × List UInt8) := do
  let (reserved8, bytes) ← Alpha.decode 8 bytes
  let (mpid, bytes) ← Alpha.decode 4 bytes
  let (clientOrderId, bytes) ← Alpha.decode 20 bytes
  let (symbolId, bytes) ← decodeUIntLE 4 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (size, bytes) ← decodeUIntLE 4 bytes
  let (newOrderInstructions, bytes) ← decodeUIntLE 2 bytes
  let (timeInForce, bytes) ← TimeInForce.decode bytes
  let (orderType, bytes) ← OrderType.decode bytes
  let (priceSlidingAndRepriceFrequency, bytes) ← PriceSlidingAndRepriceFrequency.decode bytes
  let (selfTradeProtection, bytes) ← decodeUIntLE 1 bytes
  let (selfTradeProtectionGroup, bytes) ← Alpha.decode 1 bytes
  let (routing, bytes) ← decodeUIntLE 1 bytes
  let (tradingCollarDollarValue, bytes) ← decodeUIntLE 8 bytes
  let (capacity, bytes) ← Capacity.decode bytes
  let (account, bytes) ← Alpha.decode 16 bytes
  let (clearingAccount, bytes) ← Alpha.decode 4 bytes
  let (minQty, bytes) ← decodeUIntLE 4 bytes
  let (maxFloorQty, bytes) ← decodeUIntLE 4 bytes
  let (displayRangeQty, bytes) ← decodeUIntLE 4 bytes
  let (pegOffset, bytes) ← decodeUIntLE 8 bytes
  let (locateAccount, bytes) ← Alpha.decode 4 bytes
  let (purgeGroup, bytes) ← Alpha.decode 1 bytes
  let (orderExpiryTime, bytes) ← decodeUIntLE 8 bytes
  let (reserved11, bytes) ← Alpha.decode 11 bytes
  pure ({ reserved8, mpid, clientOrderId, symbolId, price, size, newOrderInstructions, timeInForce, orderType, priceSlidingAndRepriceFrequency, selfTradeProtection, selfTradeProtectionGroup, routing, tradingCollarDollarValue, capacity, account, clearingAccount, minQty, maxFloorQty, displayRangeQty, pegOffset, locateAccount, purgeGroup, orderExpiryTime, reserved11 }, bytes)

@[simp] theorem encode_length (message : NewOrderRequestMessage) : (encode message).length = 129 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUIntLE_length, TimeInForce.encode_length, OrderType.encode_length, PriceSlidingAndRepriceFrequency.encode_length, Capacity.encode_length]

theorem encode_length_pos (message : NewOrderRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : NewOrderRequestMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, TimeInForce.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OrderType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, PriceSlidingAndRepriceFrequency.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Capacity.decode_encode, some_bind]
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end NewOrderRequestMessage

/-- Modify Order Request Message: 109 bytes -/
structure ModifyOrderRequestMessage where
  reserved8 : Alpha 8
  mpid : Alpha 4
  clientOrderId : Alpha 20
  originalClientOrderId : Alpha 20
  symbolId : BitVec 32
  price : BitVec 64
  size : BitVec 32
  modifyOrderInstructions : BitVec 8
  minQty : BitVec 32
  maxFloorQty : BitVec 32
  locateAccount : Alpha 4
  timeInForce : TimeInForce
  orderExpiryTime : BitVec 64
  reserved19 : Alpha 19
  deriving DecidableEq, Repr

namespace ModifyOrderRequestMessage

def encode (message : ModifyOrderRequestMessage) : List UInt8 :=
  Alpha.encode message.reserved8
    ++ (Alpha.encode message.mpid
    ++ (Alpha.encode message.clientOrderId
    ++ (Alpha.encode message.originalClientOrderId
    ++ (encodeUIntLE 4 message.symbolId
    ++ (encodeUIntLE 8 message.price
    ++ (encodeUIntLE 4 message.size
    ++ (encodeUIntLE 1 message.modifyOrderInstructions
    ++ (encodeUIntLE 4 message.minQty
    ++ (encodeUIntLE 4 message.maxFloorQty
    ++ (Alpha.encode message.locateAccount
    ++ (TimeInForce.encode message.timeInForce
    ++ (encodeUIntLE 8 message.orderExpiryTime
    ++ (Alpha.encode message.reserved19)))))))))))))

def decode (bytes : List UInt8) : Option (ModifyOrderRequestMessage × List UInt8) := do
  let (reserved8, bytes) ← Alpha.decode 8 bytes
  let (mpid, bytes) ← Alpha.decode 4 bytes
  let (clientOrderId, bytes) ← Alpha.decode 20 bytes
  let (originalClientOrderId, bytes) ← Alpha.decode 20 bytes
  let (symbolId, bytes) ← decodeUIntLE 4 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (size, bytes) ← decodeUIntLE 4 bytes
  let (modifyOrderInstructions, bytes) ← decodeUIntLE 1 bytes
  let (minQty, bytes) ← decodeUIntLE 4 bytes
  let (maxFloorQty, bytes) ← decodeUIntLE 4 bytes
  let (locateAccount, bytes) ← Alpha.decode 4 bytes
  let (timeInForce, bytes) ← TimeInForce.decode bytes
  let (orderExpiryTime, bytes) ← decodeUIntLE 8 bytes
  let (reserved19, bytes) ← Alpha.decode 19 bytes
  pure ({ reserved8, mpid, clientOrderId, originalClientOrderId, symbolId, price, size, modifyOrderInstructions, minQty, maxFloorQty, locateAccount, timeInForce, orderExpiryTime, reserved19 }, bytes)

@[simp] theorem encode_length (message : ModifyOrderRequestMessage) : (encode message).length = 109 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUIntLE_length, TimeInForce.encode_length]

theorem encode_length_pos (message : ModifyOrderRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ModifyOrderRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TimeInForce.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end ModifyOrderRequestMessage

/-- Cancel Order Request: 66 bytes -/
structure CancelOrderRequest where
  reserved8 : Alpha 8
  mpid : Alpha 4
  clientOrderId : Alpha 20
  originalClientOrderId : Alpha 20
  symbolId : BitVec 32
  reserved10 : Alpha 10
  deriving DecidableEq, Repr

namespace CancelOrderRequest

def encode (message : CancelOrderRequest) : List UInt8 :=
  Alpha.encode message.reserved8
    ++ (Alpha.encode message.mpid
    ++ (Alpha.encode message.clientOrderId
    ++ (Alpha.encode message.originalClientOrderId
    ++ (encodeUIntLE 4 message.symbolId
    ++ (Alpha.encode message.reserved10)))))

def decode (bytes : List UInt8) : Option (CancelOrderRequest × List UInt8) := do
  let (reserved8, bytes) ← Alpha.decode 8 bytes
  let (mpid, bytes) ← Alpha.decode 4 bytes
  let (clientOrderId, bytes) ← Alpha.decode 20 bytes
  let (originalClientOrderId, bytes) ← Alpha.decode 20 bytes
  let (symbolId, bytes) ← decodeUIntLE 4 bytes
  let (reserved10, bytes) ← Alpha.decode 10 bytes
  pure ({ reserved8, mpid, clientOrderId, originalClientOrderId, symbolId, reserved10 }, bytes)

@[simp] theorem encode_length (message : CancelOrderRequest) : (encode message).length = 66 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : CancelOrderRequest) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CancelOrderRequest) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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
  rw [Alpha.decode_encode, some_bind]
  rfl

end CancelOrderRequest

/-- Cancel Order By Exchange Order Id Request: 54 bytes -/
structure CancelOrderByExchangeOrderIdRequest where
  reserved8 : Alpha 8
  mpid : Alpha 4
  clientOrderId : Alpha 20
  orderId : BitVec 64
  symbolId : BitVec 32
  reserved10 : Alpha 10
  deriving DecidableEq, Repr

namespace CancelOrderByExchangeOrderIdRequest

def encode (message : CancelOrderByExchangeOrderIdRequest) : List UInt8 :=
  Alpha.encode message.reserved8
    ++ (Alpha.encode message.mpid
    ++ (Alpha.encode message.clientOrderId
    ++ (encodeUIntLE 8 message.orderId
    ++ (encodeUIntLE 4 message.symbolId
    ++ (Alpha.encode message.reserved10)))))

def decode (bytes : List UInt8) : Option (CancelOrderByExchangeOrderIdRequest × List UInt8) := do
  let (reserved8, bytes) ← Alpha.decode 8 bytes
  let (mpid, bytes) ← Alpha.decode 4 bytes
  let (clientOrderId, bytes) ← Alpha.decode 20 bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (symbolId, bytes) ← decodeUIntLE 4 bytes
  let (reserved10, bytes) ← Alpha.decode 10 bytes
  pure ({ reserved8, mpid, clientOrderId, orderId, symbolId, reserved10 }, bytes)

@[simp] theorem encode_length (message : CancelOrderByExchangeOrderIdRequest) : (encode message).length = 54 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : CancelOrderByExchangeOrderIdRequest) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CancelOrderByExchangeOrderIdRequest) (rest : List UInt8) :
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

end CancelOrderByExchangeOrderIdRequest

/-- Mass Cancel Request: 44 bytes -/
structure MassCancelRequest where
  reserved8 : Alpha 8
  mpid : Alpha 4
  clientOrderId : Alpha 20
  scope : Scope
  action : Action
  purgeGroup : Alpha 1
  reserved9 : Alpha 9
  deriving DecidableEq, Repr

namespace MassCancelRequest

def encode (message : MassCancelRequest) : List UInt8 :=
  Alpha.encode message.reserved8
    ++ (Alpha.encode message.mpid
    ++ (Alpha.encode message.clientOrderId
    ++ (Scope.encode message.scope
    ++ (Action.encode message.action
    ++ (Alpha.encode message.purgeGroup
    ++ (Alpha.encode message.reserved9))))))

def decode (bytes : List UInt8) : Option (MassCancelRequest × List UInt8) := do
  let (reserved8, bytes) ← Alpha.decode 8 bytes
  let (mpid, bytes) ← Alpha.decode 4 bytes
  let (clientOrderId, bytes) ← Alpha.decode 20 bytes
  let (scope, bytes) ← Scope.decode bytes
  let (action, bytes) ← Action.decode bytes
  let (purgeGroup, bytes) ← Alpha.decode 1 bytes
  let (reserved9, bytes) ← Alpha.decode 9 bytes
  pure ({ reserved8, mpid, clientOrderId, scope, action, purgeGroup, reserved9 }, bytes)

@[simp] theorem encode_length (message : MassCancelRequest) : (encode message).length = 44 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, Scope.encode_length, Action.encode_length]

theorem encode_length_pos (message : MassCancelRequest) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MassCancelRequest) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Scope.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Action.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end MassCancelRequest

/-- Mass Cancel Response: 67 bytes -/
structure MassCancelResponse where
  notificationTime : BitVec 64
  mpid : Alpha 4
  clientOrderId : Alpha 20
  numberOfMatchingEngines : BitVec 8
  matchingEngineStatus : Alpha 24
  reserved10 : Alpha 10
  deriving DecidableEq, Repr

namespace MassCancelResponse

def encode (message : MassCancelResponse) : List UInt8 :=
  encodeUIntLE 8 message.notificationTime
    ++ (Alpha.encode message.mpid
    ++ (Alpha.encode message.clientOrderId
    ++ (encodeUIntLE 1 message.numberOfMatchingEngines
    ++ (Alpha.encode message.matchingEngineStatus
    ++ (Alpha.encode message.reserved10)))))

def decode (bytes : List UInt8) : Option (MassCancelResponse × List UInt8) := do
  let (notificationTime, bytes) ← decodeUIntLE 8 bytes
  let (mpid, bytes) ← Alpha.decode 4 bytes
  let (clientOrderId, bytes) ← Alpha.decode 20 bytes
  let (numberOfMatchingEngines, bytes) ← decodeUIntLE 1 bytes
  let (matchingEngineStatus, bytes) ← Alpha.decode 24 bytes
  let (reserved10, bytes) ← Alpha.decode 10 bytes
  pure ({ notificationTime, mpid, clientOrderId, numberOfMatchingEngines, matchingEngineStatus, reserved10 }, bytes)

@[simp] theorem encode_length (message : MassCancelResponse) : (encode message).length = 67 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : MassCancelResponse) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MassCancelResponse) (rest : List UInt8) :
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

end MassCancelResponse

/-- Aggressive Side Purge Request: 56 bytes -/
structure AggressiveSidePurgeRequest where
  reserved8 : Alpha 8
  mpid : Alpha 4
  clientOrderId : Alpha 20
  symbolId : BitVec 32
  purgeInstructions : BitVec 16
  price : BitVec 64
  reserved10 : Alpha 10
  deriving DecidableEq, Repr

namespace AggressiveSidePurgeRequest

def encode (message : AggressiveSidePurgeRequest) : List UInt8 :=
  Alpha.encode message.reserved8
    ++ (Alpha.encode message.mpid
    ++ (Alpha.encode message.clientOrderId
    ++ (encodeUIntLE 4 message.symbolId
    ++ (encodeUIntLE 2 message.purgeInstructions
    ++ (encodeUIntLE 8 message.price
    ++ (Alpha.encode message.reserved10))))))

def decode (bytes : List UInt8) : Option (AggressiveSidePurgeRequest × List UInt8) := do
  let (reserved8, bytes) ← Alpha.decode 8 bytes
  let (mpid, bytes) ← Alpha.decode 4 bytes
  let (clientOrderId, bytes) ← Alpha.decode 20 bytes
  let (symbolId, bytes) ← decodeUIntLE 4 bytes
  let (purgeInstructions, bytes) ← decodeUIntLE 2 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (reserved10, bytes) ← Alpha.decode 10 bytes
  pure ({ reserved8, mpid, clientOrderId, symbolId, purgeInstructions, price, reserved10 }, bytes)

@[simp] theorem encode_length (message : AggressiveSidePurgeRequest) : (encode message).length = 56 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : AggressiveSidePurgeRequest) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : AggressiveSidePurgeRequest) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end AggressiveSidePurgeRequest

/-- Aggressive Side Purge Response: 49 bytes -/
structure AggressiveSidePurgeResponse where
  matchingEngineTime : BitVec 64
  mpid : Alpha 4
  clientOrderId : Alpha 20
  symboldId : BitVec 32
  purgeStatus : PurgeStatus
  numberOfOrdersCancelled : BitVec 8
  aspEligibleOrdersCancelled : Alpha 1
  reserved10 : Alpha 10
  deriving DecidableEq, Repr

namespace AggressiveSidePurgeResponse

def encode (message : AggressiveSidePurgeResponse) : List UInt8 :=
  encodeUIntLE 8 message.matchingEngineTime
    ++ (Alpha.encode message.mpid
    ++ (Alpha.encode message.clientOrderId
    ++ (encodeUIntLE 4 message.symboldId
    ++ (PurgeStatus.encode message.purgeStatus
    ++ (encodeUIntLE 1 message.numberOfOrdersCancelled
    ++ (Alpha.encode message.aspEligibleOrdersCancelled
    ++ (Alpha.encode message.reserved10)))))))

def decode (bytes : List UInt8) : Option (AggressiveSidePurgeResponse × List UInt8) := do
  let (matchingEngineTime, bytes) ← decodeUIntLE 8 bytes
  let (mpid, bytes) ← Alpha.decode 4 bytes
  let (clientOrderId, bytes) ← Alpha.decode 20 bytes
  let (symboldId, bytes) ← decodeUIntLE 4 bytes
  let (purgeStatus, bytes) ← PurgeStatus.decode bytes
  let (numberOfOrdersCancelled, bytes) ← decodeUIntLE 1 bytes
  let (aspEligibleOrdersCancelled, bytes) ← Alpha.decode 1 bytes
  let (reserved10, bytes) ← Alpha.decode 10 bytes
  pure ({ matchingEngineTime, mpid, clientOrderId, symboldId, purgeStatus, numberOfOrdersCancelled, aspEligibleOrdersCancelled, reserved10 }, bytes)

@[simp] theorem encode_length (message : AggressiveSidePurgeResponse) : (encode message).length = 49 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, PurgeStatus.encode_length]

theorem encode_length_pos (message : AggressiveSidePurgeResponse) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : AggressiveSidePurgeResponse) (rest : List UInt8) :
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
  rw [List.append_assoc, PurgeStatus.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end AggressiveSidePurgeResponse

/-- Any Unsequenced Message, selected by Unsequenced Message Type -/
inductive UnsequencedMessage where
  | newOrderRequestMessage (message : NewOrderRequestMessage) -- "N1" 0x4E31
  | newOrderResponseMessage (message : NewOrderResponseMessage) -- "NR" 0x4E52
  | modifyOrderRequestMessage (message : ModifyOrderRequestMessage) -- "M1" 0x4D31
  | modifyOrderResponse (message : ModifyOrderResponse) -- "MR" 0x4D52
  | cancelOrderRequest (message : CancelOrderRequest) -- "CO" 0x434F
  | cancelOrderResponse (message : CancelOrderResponse) -- "CR" 0x4352
  | cancelOrderByExchangeOrderIdRequest (message : CancelOrderByExchangeOrderIdRequest) -- "CX" 0x4358
  | cancelOrderByExchangeOrderIdResponseMessage (message : CancelOrderByExchangeOrderIdResponseMessage) -- "CQ" 0x4351
  | massCancelRequest (message : MassCancelRequest) -- "XQ" 0x5851
  | massCancelResponse (message : MassCancelResponse) -- "XR" 0x5852
  | aggressiveSidePurgeRequest (message : AggressiveSidePurgeRequest) -- "XS" 0x5853
  | aggressiveSidePurgeResponse (message : AggressiveSidePurgeResponse) -- "SR" 0x5352
  | reserveOrderReplenishmentNotification (message : ReserveOrderReplenishmentNotification) -- "RA" 0x5241
  | executionNotification (message : ExecutionNotification) -- "E1" 0x4531
  deriving DecidableEq, Repr

namespace UnsequencedMessage

/-- The Unsequenced Message Type each message is sent under -/
def tag : UnsequencedMessage → BitVec 16
  | .newOrderRequestMessage _ => 20017
  | .newOrderResponseMessage _ => 20050
  | .modifyOrderRequestMessage _ => 19761
  | .modifyOrderResponse _ => 19794
  | .cancelOrderRequest _ => 17231
  | .cancelOrderResponse _ => 17234
  | .cancelOrderByExchangeOrderIdRequest _ => 17240
  | .cancelOrderByExchangeOrderIdResponseMessage _ => 17233
  | .massCancelRequest _ => 22609
  | .massCancelResponse _ => 22610
  | .aggressiveSidePurgeRequest _ => 22611
  | .aggressiveSidePurgeResponse _ => 21330
  | .reserveOrderReplenishmentNotification _ => 21057
  | .executionNotification _ => 17713

def encode : UnsequencedMessage → List UInt8
  | .newOrderRequestMessage message => NewOrderRequestMessage.encode message
  | .newOrderResponseMessage message => NewOrderResponseMessage.encode message
  | .modifyOrderRequestMessage message => ModifyOrderRequestMessage.encode message
  | .modifyOrderResponse message => ModifyOrderResponse.encode message
  | .cancelOrderRequest message => CancelOrderRequest.encode message
  | .cancelOrderResponse message => CancelOrderResponse.encode message
  | .cancelOrderByExchangeOrderIdRequest message => CancelOrderByExchangeOrderIdRequest.encode message
  | .cancelOrderByExchangeOrderIdResponseMessage message => CancelOrderByExchangeOrderIdResponseMessage.encode message
  | .massCancelRequest message => MassCancelRequest.encode message
  | .massCancelResponse message => MassCancelResponse.encode message
  | .aggressiveSidePurgeRequest message => AggressiveSidePurgeRequest.encode message
  | .aggressiveSidePurgeResponse message => AggressiveSidePurgeResponse.encode message
  | .reserveOrderReplenishmentNotification message => ReserveOrderReplenishmentNotification.encode message
  | .executionNotification message => ExecutionNotification.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : UnsequencedMessage) : (encode message).length ≤ 129 := by
  cases message with
  | newOrderRequestMessage inner =>
    simp only [encode, NewOrderRequestMessage.encode_length]
    omega
  | newOrderResponseMessage inner =>
    simp only [encode, NewOrderResponseMessage.encode_length]
    omega
  | modifyOrderRequestMessage inner =>
    simp only [encode, ModifyOrderRequestMessage.encode_length]
    omega
  | modifyOrderResponse inner =>
    simp only [encode, ModifyOrderResponse.encode_length]
    omega
  | cancelOrderRequest inner =>
    simp only [encode, CancelOrderRequest.encode_length]
    omega
  | cancelOrderResponse inner =>
    simp only [encode, CancelOrderResponse.encode_length]
    omega
  | cancelOrderByExchangeOrderIdRequest inner =>
    simp only [encode, CancelOrderByExchangeOrderIdRequest.encode_length]
    omega
  | cancelOrderByExchangeOrderIdResponseMessage inner =>
    simp only [encode, CancelOrderByExchangeOrderIdResponseMessage.encode_length]
    omega
  | massCancelRequest inner =>
    simp only [encode, MassCancelRequest.encode_length]
    omega
  | massCancelResponse inner =>
    simp only [encode, MassCancelResponse.encode_length]
    omega
  | aggressiveSidePurgeRequest inner =>
    simp only [encode, AggressiveSidePurgeRequest.encode_length]
    omega
  | aggressiveSidePurgeResponse inner =>
    simp only [encode, AggressiveSidePurgeResponse.encode_length]
    omega
  | reserveOrderReplenishmentNotification inner =>
    simp only [encode, ReserveOrderReplenishmentNotification.encode_length]
    omega
  | executionNotification inner =>
    simp only [encode, ExecutionNotification.encode_length]
    omega

def decode (tag : BitVec 16) (bytes : List UInt8) : Option (UnsequencedMessage × List UInt8) :=
  if tag = 20017 then (NewOrderRequestMessage.decode bytes).map fun (message, rest) => (.newOrderRequestMessage message, rest)
  else if tag = 20050 then (NewOrderResponseMessage.decode bytes).map fun (message, rest) => (.newOrderResponseMessage message, rest)
  else if tag = 19761 then (ModifyOrderRequestMessage.decode bytes).map fun (message, rest) => (.modifyOrderRequestMessage message, rest)
  else if tag = 19794 then (ModifyOrderResponse.decode bytes).map fun (message, rest) => (.modifyOrderResponse message, rest)
  else if tag = 17231 then (CancelOrderRequest.decode bytes).map fun (message, rest) => (.cancelOrderRequest message, rest)
  else if tag = 17234 then (CancelOrderResponse.decode bytes).map fun (message, rest) => (.cancelOrderResponse message, rest)
  else if tag = 17240 then (CancelOrderByExchangeOrderIdRequest.decode bytes).map fun (message, rest) => (.cancelOrderByExchangeOrderIdRequest message, rest)
  else if tag = 17233 then (CancelOrderByExchangeOrderIdResponseMessage.decode bytes).map fun (message, rest) => (.cancelOrderByExchangeOrderIdResponseMessage message, rest)
  else if tag = 22609 then (MassCancelRequest.decode bytes).map fun (message, rest) => (.massCancelRequest message, rest)
  else if tag = 22610 then (MassCancelResponse.decode bytes).map fun (message, rest) => (.massCancelResponse message, rest)
  else if tag = 22611 then (AggressiveSidePurgeRequest.decode bytes).map fun (message, rest) => (.aggressiveSidePurgeRequest message, rest)
  else if tag = 21330 then (AggressiveSidePurgeResponse.decode bytes).map fun (message, rest) => (.aggressiveSidePurgeResponse message, rest)
  else if tag = 21057 then (ReserveOrderReplenishmentNotification.decode bytes).map fun (message, rest) => (.reserveOrderReplenishmentNotification message, rest)
  else if tag = 17713 then (ExecutionNotification.decode bytes).map fun (message, rest) => (.executionNotification message, rest)
  else none

@[simp] theorem decode_encode (message : UnsequencedMessage) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end UnsequencedMessage

/-- Unsequenced Data Packet -/
structure UnsequencedDataPacket where
  unsequencedMessage : UnsequencedMessage
  deriving DecidableEq, Repr

namespace UnsequencedDataPacket

def encode (message : UnsequencedDataPacket) : List UInt8 :=
  encodeUInt 2 (UnsequencedMessage.tag message.unsequencedMessage)
    ++ (UnsequencedMessage.encode message.unsequencedMessage)

def decode (bytes : List UInt8) : Option (UnsequencedDataPacket × List UInt8) := do
  let (unsequencedMessageType, bytes) ← decodeUInt 2 bytes
  let (unsequencedMessage, bytes) ← UnsequencedMessage.decode unsequencedMessageType bytes
  pure ({ unsequencedMessage }, bytes)

theorem encode_length_pos (message : UnsequencedDataPacket) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : UnsequencedDataPacket) : (encode message).length ≤ 131 := by
  unfold encode
  cases message.unsequencedMessage with
  | newOrderRequestMessage inner =>
    simp only [UnsequencedMessage.encode, List.length_append, encodeUInt_length, NewOrderRequestMessage.encode_length]
    omega
  | newOrderResponseMessage inner =>
    simp only [UnsequencedMessage.encode, List.length_append, encodeUInt_length, NewOrderResponseMessage.encode_length]
    omega
  | modifyOrderRequestMessage inner =>
    simp only [UnsequencedMessage.encode, List.length_append, encodeUInt_length, ModifyOrderRequestMessage.encode_length]
    omega
  | modifyOrderResponse inner =>
    simp only [UnsequencedMessage.encode, List.length_append, encodeUInt_length, ModifyOrderResponse.encode_length]
    omega
  | cancelOrderRequest inner =>
    simp only [UnsequencedMessage.encode, List.length_append, encodeUInt_length, CancelOrderRequest.encode_length]
    omega
  | cancelOrderResponse inner =>
    simp only [UnsequencedMessage.encode, List.length_append, encodeUInt_length, CancelOrderResponse.encode_length]
    omega
  | cancelOrderByExchangeOrderIdRequest inner =>
    simp only [UnsequencedMessage.encode, List.length_append, encodeUInt_length, CancelOrderByExchangeOrderIdRequest.encode_length]
    omega
  | cancelOrderByExchangeOrderIdResponseMessage inner =>
    simp only [UnsequencedMessage.encode, List.length_append, encodeUInt_length, CancelOrderByExchangeOrderIdResponseMessage.encode_length]
    omega
  | massCancelRequest inner =>
    simp only [UnsequencedMessage.encode, List.length_append, encodeUInt_length, MassCancelRequest.encode_length]
    omega
  | massCancelResponse inner =>
    simp only [UnsequencedMessage.encode, List.length_append, encodeUInt_length, MassCancelResponse.encode_length]
    omega
  | aggressiveSidePurgeRequest inner =>
    simp only [UnsequencedMessage.encode, List.length_append, encodeUInt_length, AggressiveSidePurgeRequest.encode_length]
    omega
  | aggressiveSidePurgeResponse inner =>
    simp only [UnsequencedMessage.encode, List.length_append, encodeUInt_length, AggressiveSidePurgeResponse.encode_length]
    omega
  | reserveOrderReplenishmentNotification inner =>
    simp only [UnsequencedMessage.encode, List.length_append, encodeUInt_length, ReserveOrderReplenishmentNotification.encode_length]
    omega
  | executionNotification inner =>
    simp only [UnsequencedMessage.encode, List.length_append, encodeUInt_length, ExecutionNotification.encode_length]
    omega

@[simp] theorem decode_encode (message : UnsequencedDataPacket) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [UnsequencedMessage.decode_encode, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : UnsequencedDataPacket) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end UnsequencedDataPacket

/-- Login Request: 35 bytes -/
structure LoginRequest where
  esesmVersion : Alpha 5
  username : Alpha 5
  computerId : Alpha 8
  applicationProtocol : Alpha 8
  requestedTradingSessionId : BitVec 8
  requestedSequenceNumber : BitVec 64
  deriving DecidableEq, Repr

namespace LoginRequest

def encode (message : LoginRequest) : List UInt8 :=
  Alpha.encode message.esesmVersion
    ++ (Alpha.encode message.username
    ++ (Alpha.encode message.computerId
    ++ (Alpha.encode message.applicationProtocol
    ++ (encodeUInt 1 message.requestedTradingSessionId
    ++ (encodeUIntLE 8 message.requestedSequenceNumber)))))

def decode (bytes : List UInt8) : Option (LoginRequest × List UInt8) := do
  let (esesmVersion, bytes) ← Alpha.decode 5 bytes
  let (username, bytes) ← Alpha.decode 5 bytes
  let (computerId, bytes) ← Alpha.decode 8 bytes
  let (applicationProtocol, bytes) ← Alpha.decode 8 bytes
  let (requestedTradingSessionId, bytes) ← decodeUInt 1 bytes
  let (requestedSequenceNumber, bytes) ← decodeUIntLE 8 bytes
  pure ({ esesmVersion, username, computerId, applicationProtocol, requestedTradingSessionId, requestedSequenceNumber }, bytes)

@[simp] theorem encode_length (message : LoginRequest) : (encode message).length = 35 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length, encodeUIntLE_length]

theorem encode_length_pos (message : LoginRequest) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LoginRequest) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : LoginRequest) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end LoginRequest

/-- Login Response: 11 bytes -/
structure LoginResponse where
  numberOfMatchingEngines : BitVec 8
  loginStatus : LoginStatus
  tradingSessionId : BitVec 8
  highestSequenceNumber : BitVec 64
  deriving DecidableEq, Repr

namespace LoginResponse

def encode (message : LoginResponse) : List UInt8 :=
  encodeUIntLE 1 message.numberOfMatchingEngines
    ++ (LoginStatus.encode message.loginStatus
    ++ (encodeUInt 1 message.tradingSessionId
    ++ (encodeUIntLE 8 message.highestSequenceNumber)))

def decode (bytes : List UInt8) : Option (LoginResponse × List UInt8) := do
  let (numberOfMatchingEngines, bytes) ← decodeUIntLE 1 bytes
  let (loginStatus, bytes) ← LoginStatus.decode bytes
  let (tradingSessionId, bytes) ← decodeUInt 1 bytes
  let (highestSequenceNumber, bytes) ← decodeUIntLE 8 bytes
  pure ({ numberOfMatchingEngines, loginStatus, tradingSessionId, highestSequenceNumber }, bytes)

@[simp] theorem encode_length (message : LoginResponse) : (encode message).length = 11 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, LoginStatus.encode_length, encodeUInt_length]

theorem encode_length_pos (message : LoginResponse) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LoginResponse) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, LoginStatus.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : LoginResponse) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end LoginResponse

/-- Synchronization Complete: 1 bytes -/
structure SynchronizationComplete where
  numberOfMatchingEngines : BitVec 8
  deriving DecidableEq, Repr

namespace SynchronizationComplete

def encode (message : SynchronizationComplete) : List UInt8 :=
  encodeUIntLE 1 message.numberOfMatchingEngines

def decode (bytes : List UInt8) : Option (SynchronizationComplete × List UInt8) := do
  let (numberOfMatchingEngines, bytes) ← decodeUIntLE 1 bytes
  pure ({ numberOfMatchingEngines }, bytes)

@[simp] theorem encode_length (message : SynchronizationComplete) : (encode message).length = 1 := by
  unfold encode
  simp only [encodeUIntLE_length]

theorem encode_length_pos (message : SynchronizationComplete) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SynchronizationComplete) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : SynchronizationComplete) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end SynchronizationComplete

/-- Retransmission Request: 16 bytes -/
structure RetransmissionRequest where
  startSequenceNumber : BitVec 64
  endSequenceNumber : BitVec 64
  deriving DecidableEq, Repr

namespace RetransmissionRequest

def encode (message : RetransmissionRequest) : List UInt8 :=
  encodeUIntLE 8 message.startSequenceNumber
    ++ (encodeUIntLE 8 message.endSequenceNumber)

def decode (bytes : List UInt8) : Option (RetransmissionRequest × List UInt8) := do
  let (startSequenceNumber, bytes) ← decodeUIntLE 8 bytes
  let (endSequenceNumber, bytes) ← decodeUIntLE 8 bytes
  pure ({ startSequenceNumber, endSequenceNumber }, bytes)

@[simp] theorem encode_length (message : RetransmissionRequest) : (encode message).length = 16 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : RetransmissionRequest) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : RetransmissionRequest) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : RetransmissionRequest) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end RetransmissionRequest

/-- Logout Request -/
structure LogoutRequest where
  logoutReason : LogoutReason
  logoutText : Capped 65386
  deriving DecidableEq, Repr

namespace LogoutRequest

def encode (message : LogoutRequest) : List UInt8 :=
  LogoutReason.encode message.logoutReason
    ++ (message.logoutText.val)

def decode (bytes : List UInt8) : Option LogoutRequest := do
  let (logoutReason, bytes) ← LogoutReason.decode bytes
  let logoutText_ := bytes
  if fits_logoutText : logoutText_.length ≤ 65386 then
    pure { logoutReason, logoutText := ⟨logoutText_, fits_logoutText⟩ }
  else none

theorem encode_length_pos (message : LogoutRequest) : (encode message).length > 0 := by
  unfold encode
  simp only [LogoutReason.encode_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : LogoutRequest) : (encode message).length ≤ 65387 := by
  have bound_logoutText := message.logoutText.length_le
  unfold encode
  simp only [List.length_append, LogoutReason.encode_length]
  omega

theorem decode_encode (message : LogoutRequest) : decode (encode message) = some message := by
  unfold decode encode
  rw [LogoutReason.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.logoutText.length_le]
  rfl

end LogoutRequest

/-- Goodbye Packet -/
structure GoodbyePacket where
  logoutReason : LogoutReason
  logoutText : Capped 65386
  deriving DecidableEq, Repr

namespace GoodbyePacket

def encode (message : GoodbyePacket) : List UInt8 :=
  LogoutReason.encode message.logoutReason
    ++ (message.logoutText.val)

def decode (bytes : List UInt8) : Option GoodbyePacket := do
  let (logoutReason, bytes) ← LogoutReason.decode bytes
  let logoutText_ := bytes
  if fits_logoutText : logoutText_.length ≤ 65386 then
    pure { logoutReason, logoutText := ⟨logoutText_, fits_logoutText⟩ }
  else none

theorem encode_length_pos (message : GoodbyePacket) : (encode message).length > 0 := by
  unfold encode
  simp only [LogoutReason.encode_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : GoodbyePacket) : (encode message).length ≤ 65387 := by
  have bound_logoutText := message.logoutText.length_le
  unfold encode
  simp only [List.length_append, LogoutReason.encode_length]
  omega

theorem decode_encode (message : GoodbyePacket) : decode (encode message) = some message := by
  unfold decode encode
  rw [LogoutReason.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.logoutText.length_le]
  rfl

end GoodbyePacket

/-- Trading Session Update: 0 bytes -/
structure TradingSessionUpdate where
  deriving DecidableEq, Repr

namespace TradingSessionUpdate

def encode (_ : TradingSessionUpdate) : List UInt8 :=
  []

def decode (bytes : List UInt8) : Option (TradingSessionUpdate × List UInt8) :=
  some (⟨⟩, bytes)

@[simp] theorem encode_length (message : TradingSessionUpdate) : (encode message).length = 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : TradingSessionUpdate) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode]

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : TradingSessionUpdate) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end TradingSessionUpdate

/-- Server Heartbeat: 0 bytes -/
structure ServerHeartbeat where
  deriving DecidableEq, Repr

namespace ServerHeartbeat

def encode (_ : ServerHeartbeat) : List UInt8 :=
  []

def decode (bytes : List UInt8) : Option (ServerHeartbeat × List UInt8) :=
  some (⟨⟩, bytes)

@[simp] theorem encode_length (message : ServerHeartbeat) : (encode message).length = 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : ServerHeartbeat) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode]

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : ServerHeartbeat) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end ServerHeartbeat

/-- Client Heartbeat: 0 bytes -/
structure ClientHeartbeat where
  deriving DecidableEq, Repr

namespace ClientHeartbeat

def encode (_ : ClientHeartbeat) : List UInt8 :=
  []

def decode (bytes : List UInt8) : Option (ClientHeartbeat × List UInt8) :=
  some (⟨⟩, bytes)

@[simp] theorem encode_length (message : ClientHeartbeat) : (encode message).length = 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : ClientHeartbeat) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode]

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : ClientHeartbeat) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end ClientHeartbeat

/-- Test Packet -/
structure TestPacket where
  testText : Capped 65386
  deriving DecidableEq, Repr

namespace TestPacket

def encode (message : TestPacket) : List UInt8 :=
  message.testText.val

def decode (bytes : List UInt8) : Option TestPacket := do
  let testText_ := bytes
  if fits_testText : testText_.length ≤ 65386 then
    pure { testText := ⟨testText_, fits_testText⟩ }
  else none

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : TestPacket) : (encode message).length ≤ 65386 := by
  have bound_testText := message.testText.length_le
  unfold encode
  omega

theorem decode_encode (message : TestPacket) : decode (encode message) = some message := by
  unfold decode encode
  rw [dite_eq_left message.testText.length_le]
  rfl

end TestPacket

/-- Any Esesm Payload, selected by Esesm Packet Type -/
inductive EsesmPayload where
  | sequencedDataPacket (message : SequencedDataPacket) -- "s" 0x73
  | unsequencedDataPacket (message : UnsequencedDataPacket) -- "U" 0x55
  | loginRequest (message : LoginRequest) -- "l" 0x6C
  | loginResponse (message : LoginResponse) -- "r" 0x72
  | synchronizationComplete (message : SynchronizationComplete) -- "c" 0x63
  | retransmissionRequest (message : RetransmissionRequest) -- "a" 0x61
  | logoutRequest (message : LogoutRequest) -- "X" 0x58
  | goodbyePacket (message : GoodbyePacket) -- "G" 0x47
  | tradingSessionUpdate (message : TradingSessionUpdate) -- "u" 0x75
  | serverHeartbeat (message : ServerHeartbeat) -- "0" 0x30
  | clientHeartbeat (message : ClientHeartbeat) -- "1" 0x31
  | testPacket (message : TestPacket) -- "T" 0x54
  deriving DecidableEq, Repr

namespace EsesmPayload

/-- The Esesm Packet Type each message is sent under -/
def tag : EsesmPayload → BitVec 8
  | .sequencedDataPacket _ => 115
  | .unsequencedDataPacket _ => 85
  | .loginRequest _ => 108
  | .loginResponse _ => 114
  | .synchronizationComplete _ => 99
  | .retransmissionRequest _ => 97
  | .logoutRequest _ => 88
  | .goodbyePacket _ => 71
  | .tradingSessionUpdate _ => 117
  | .serverHeartbeat _ => 48
  | .clientHeartbeat _ => 49
  | .testPacket _ => 84

def encode : EsesmPayload → List UInt8
  | .sequencedDataPacket message => SequencedDataPacket.encode message
  | .unsequencedDataPacket message => UnsequencedDataPacket.encode message
  | .loginRequest message => LoginRequest.encode message
  | .loginResponse message => LoginResponse.encode message
  | .synchronizationComplete message => SynchronizationComplete.encode message
  | .retransmissionRequest message => RetransmissionRequest.encode message
  | .logoutRequest message => LogoutRequest.encode message
  | .goodbyePacket message => GoodbyePacket.encode message
  | .tradingSessionUpdate message => TradingSessionUpdate.encode message
  | .serverHeartbeat message => ServerHeartbeat.encode message
  | .clientHeartbeat message => ClientHeartbeat.encode message
  | .testPacket message => TestPacket.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : EsesmPayload) : (encode message).length ≤ 65387 := by
  cases message with
  | sequencedDataPacket inner =>
    have bound_inner := SequencedDataPacket.encode_length_le inner
    simp only [encode]
    omega
  | unsequencedDataPacket inner =>
    have bound_inner := UnsequencedDataPacket.encode_length_le inner
    simp only [encode]
    omega
  | loginRequest inner =>
    simp only [encode, LoginRequest.encode_length]
    omega
  | loginResponse inner =>
    simp only [encode, LoginResponse.encode_length]
    omega
  | synchronizationComplete inner =>
    simp only [encode, SynchronizationComplete.encode_length]
    omega
  | retransmissionRequest inner =>
    simp only [encode, RetransmissionRequest.encode_length]
    omega
  | logoutRequest inner =>
    have bound_inner := LogoutRequest.encode_length_le inner
    simp only [encode]
    omega
  | goodbyePacket inner =>
    have bound_inner := GoodbyePacket.encode_length_le inner
    simp only [encode]
    omega
  | tradingSessionUpdate inner =>
    simp only [encode, TradingSessionUpdate.encode_length]
    omega
  | serverHeartbeat inner =>
    simp only [encode, ServerHeartbeat.encode_length]
    omega
  | clientHeartbeat inner =>
    simp only [encode, ClientHeartbeat.encode_length]
    omega
  | testPacket inner =>
    have bound_inner := TestPacket.encode_length_le inner
    simp only [encode]
    omega

/-- Decoded from the whole of the frame: a message that reads to its end takes it all, any other must leave nothing -/
def decode (tag : BitVec 8) (bytes : List UInt8) : Option EsesmPayload :=
  if tag = 115 then (SequencedDataPacket.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.sequencedDataPacket message) else none
  else if tag = 85 then (UnsequencedDataPacket.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.unsequencedDataPacket message) else none
  else if tag = 108 then (LoginRequest.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.loginRequest message) else none
  else if tag = 114 then (LoginResponse.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.loginResponse message) else none
  else if tag = 99 then (SynchronizationComplete.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.synchronizationComplete message) else none
  else if tag = 97 then (RetransmissionRequest.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.retransmissionRequest message) else none
  else if tag = 88 then (LogoutRequest.decode bytes).map fun message => .logoutRequest message
  else if tag = 71 then (GoodbyePacket.decode bytes).map fun message => .goodbyePacket message
  else if tag = 117 then (TradingSessionUpdate.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.tradingSessionUpdate message) else none
  else if tag = 48 then (ServerHeartbeat.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.serverHeartbeat message) else none
  else if tag = 49 then (ClientHeartbeat.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.clientHeartbeat message) else none
  else if tag = 84 then (TestPacket.decode bytes).map fun message => .testPacket message
  else none

theorem decode_encode (message : EsesmPayload) :
    decode (tag message) (encode message) = some message := by
  cases message with
  | sequencedDataPacket message => simp [decode, encode, tag, SequencedDataPacket.decode_encode_nil]
  | unsequencedDataPacket message => simp [decode, encode, tag, UnsequencedDataPacket.decode_encode_nil]
  | loginRequest message => simp [decode, encode, tag, LoginRequest.decode_encode_nil]
  | loginResponse message => simp [decode, encode, tag, LoginResponse.decode_encode_nil]
  | synchronizationComplete message => simp [decode, encode, tag, SynchronizationComplete.decode_encode_nil]
  | retransmissionRequest message => simp [decode, encode, tag, RetransmissionRequest.decode_encode_nil]
  | logoutRequest message => simp [decode, encode, tag, LogoutRequest.decode_encode]
  | goodbyePacket message => simp [decode, encode, tag, GoodbyePacket.decode_encode]
  | tradingSessionUpdate message => simp [decode, encode, tag, TradingSessionUpdate.decode_encode_nil]
  | serverHeartbeat message => simp [decode, encode, tag, ServerHeartbeat.decode_encode_nil]
  | clientHeartbeat message => simp [decode, encode, tag, ClientHeartbeat.decode_encode_nil]
  | testPacket message => simp [decode, encode, tag, TestPacket.decode_encode]

end EsesmPayload

/-- Esesm Tcp Packet -/
structure EsesmTcpPacket where
  esesmPayload : EsesmPayload
  deriving DecidableEq, Repr

namespace EsesmTcpPacket

def encodeBody (message : EsesmTcpPacket) : List UInt8 :=
  encodeUInt 1 (EsesmPayload.tag message.esesmPayload)
    ++ (EsesmPayload.encode message.esesmPayload)

def decodeBody (bytes : List UInt8) : Option EsesmTcpPacket := do
  let (esesmPacketType, bytes) ← decodeUInt 1 bytes
  let esesmPayload ← EsesmPayload.decode esesmPacketType bytes
  pure { esesmPayload }

theorem decodeBody_encodeBody (message : EsesmTcpPacket) : decodeBody (encodeBody message) = some message := by
  unfold decodeBody encodeBody
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [EsesmPayload.decode_encode, some_bind]
  rfl

/-- Every body fits the length prefix -/
theorem encodeBody_length_lt (message : EsesmTcpPacket) : (encodeBody message).length + 0 < 256 ^ 2 := by
  unfold encodeBody
  cases message.esesmPayload with
  | sequencedDataPacket inner =>
    have bound_inner := SequencedDataPacket.encode_length_le inner
    simp only [EsesmPayload.encode, List.length_append, encodeUInt_length]
    omega
  | unsequencedDataPacket inner =>
    have bound_inner := UnsequencedDataPacket.encode_length_le inner
    simp only [EsesmPayload.encode, List.length_append, encodeUInt_length]
    omega
  | loginRequest inner =>
    simp only [EsesmPayload.encode, List.length_append, encodeUInt_length, LoginRequest.encode_length]
    omega
  | loginResponse inner =>
    simp only [EsesmPayload.encode, List.length_append, encodeUInt_length, LoginResponse.encode_length]
    omega
  | synchronizationComplete inner =>
    simp only [EsesmPayload.encode, List.length_append, encodeUInt_length, SynchronizationComplete.encode_length]
    omega
  | retransmissionRequest inner =>
    simp only [EsesmPayload.encode, List.length_append, encodeUInt_length, RetransmissionRequest.encode_length]
    omega
  | logoutRequest inner =>
    have bound_inner := LogoutRequest.encode_length_le inner
    simp only [EsesmPayload.encode, List.length_append, encodeUInt_length]
    omega
  | goodbyePacket inner =>
    have bound_inner := GoodbyePacket.encode_length_le inner
    simp only [EsesmPayload.encode, List.length_append, encodeUInt_length]
    omega
  | tradingSessionUpdate inner =>
    simp only [EsesmPayload.encode, List.length_append, encodeUInt_length, TradingSessionUpdate.encode_length]
    omega
  | serverHeartbeat inner =>
    simp only [EsesmPayload.encode, List.length_append, encodeUInt_length, ServerHeartbeat.encode_length]
    omega
  | clientHeartbeat inner =>
    simp only [EsesmPayload.encode, List.length_append, encodeUInt_length, ClientHeartbeat.encode_length]
    omega
  | testPacket inner =>
    have bound_inner := TestPacket.encode_length_le inner
    simp only [EsesmPayload.encode, List.length_append, encodeUInt_length]
    omega

/-- Size rule: Esesm Packet Length counts the bytes after it, so it is written from the body and checked on decode -/
def encode : EsesmTcpPacket → List UInt8 :=
  encodeFramedLE 2 0 encodeBody

def decode : List UInt8 → Option (EsesmTcpPacket × List UInt8) :=
  decodeFramedAllLE 2 0 decodeBody

@[simp] theorem decode_encode (message : EsesmTcpPacket) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) :=
  decodeFramedAllLE_encodeFramedLE 2 0 encodeBody decodeBody message (decodeBody_encodeBody message) (encodeBody_length_lt message) rest

theorem encode_length_pos (message : EsesmTcpPacket) : (encode message).length > 0 := by
  unfold encode
  rw [encodeFramedLE_length]
  omega

end EsesmTcpPacket

/-- Packet -/
structure Packet where
  esesmTcpPacket : List EsesmTcpPacket
  deriving DecidableEq, Repr

namespace Packet

def encode (message : Packet) : List UInt8 :=
  encodeMany EsesmTcpPacket.encode message.esesmTcpPacket

def decode (bytes : List UInt8) : Option Packet := do
  let esesmTcpPacket ← decodeAll EsesmTcpPacket.decode bytes.length bytes
  pure { esesmTcpPacket }

theorem decode_encode (message : Packet) : decode (encode message) = some message := by
  unfold decode encode
  rw [decodeAll_encodeMany EsesmTcpPacket.encode EsesmTcpPacket.decode EsesmTcpPacket.decode_encode EsesmTcpPacket.encode_length_pos message.esesmTcpPacket _ (encodeMany_length_ge EsesmTcpPacket.encode EsesmTcpPacket.encode_length_pos message.esesmTcpPacket), some_bind]
  rfl

end Packet

end Omi.MiaxPearlequitiesExpressordersMeoV27
