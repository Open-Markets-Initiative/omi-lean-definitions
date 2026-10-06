import Wire

/-!
# Nextrade Nextrade Etp Market Data 10 Level v2.12

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.NextradeNextradeEtp10levelNxtasciiV212

/-- Polling Data Message: 5 bytes -/
structure PollingDataMessage where
  currentTime1MinuteInterval : Alpha 4
  endKeyword : Alpha 1
  deriving DecidableEq, Repr

namespace PollingDataMessage

def encode (message : PollingDataMessage) : List UInt8 :=
  Alpha.encode message.currentTime1MinuteInterval
    ++ (Alpha.encode message.endKeyword)

def decode (bytes : List UInt8) : Option (PollingDataMessage × List UInt8) := do
  let (currentTime1MinuteInterval, bytes) ← Alpha.decode 4 bytes
  let (endKeyword, bytes) ← Alpha.decode 1 bytes
  pure ({ currentTime1MinuteInterval, endKeyword }, bytes)

@[simp] theorem encode_length (message : PollingDataMessage) : (encode message).length = 5 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : PollingDataMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : PollingDataMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end PollingDataMessage

/-- Securities Quote Mm Lp Quotes Included 10 Level Message: 825 bytes -/
structure SecuritiesQuoteMmLpQuotesIncluded10LevelMessage where
  messageSequenceNumber : Alpha 8
  boardId : Alpha 2
  sessionId : Alpha 2
  isinCode : Alpha 12
  aDesignatedNumberForAnIssueFromKrx : Alpha 6
  processingTimeOfTradingSystem : Alpha 12
  askLevel1Price : Alpha 11
  bidLevel1Price : Alpha 11
  askLevel1Volume : Alpha 12
  bidLevel1Volume : Alpha 12
  lpAskLevel1Volume : Alpha 12
  lpBidLevel1Volume : Alpha 12
  askLevel2Price : Alpha 11
  bidLevel2Price : Alpha 11
  askLevel2Volume : Alpha 12
  bidLevel2Volume : Alpha 12
  lpAskLevel2Volume : Alpha 12
  lpBidLevel2Volume : Alpha 12
  askLevel3Price : Alpha 11
  bidLevel3Price : Alpha 11
  askLevel3Volume : Alpha 12
  bidLevel3Volume : Alpha 12
  lpAskLevel3Volume : Alpha 12
  lpBidLevel3Volume : Alpha 12
  askLevel4Price : Alpha 11
  bidLevel4Price : Alpha 11
  askLevel4Volume : Alpha 12
  bidLevel4Volume : Alpha 12
  lpAskLevel4Volume : Alpha 12
  lpBidLevel4Volume : Alpha 12
  askLevel5Price : Alpha 11
  bidLevel5Price : Alpha 11
  askLevel5Volume : Alpha 12
  bidLevel5Volume : Alpha 12
  lpAskLevel5Volume : Alpha 12
  lpBidLevel5Volume : Alpha 12
  askLevel6Price : Alpha 11
  bidLevel6Price : Alpha 11
  askLevel6Volume : Alpha 12
  bidLevel6Volume : Alpha 12
  lpAskLevel6Volume : Alpha 12
  lpBidLevel6Volume : Alpha 12
  askLevel7Price : Alpha 11
  bidLevel7Price : Alpha 11
  askLevel7Volume : Alpha 12
  bidLevel7Volume : Alpha 12
  lpAskLevel7Volume : Alpha 12
  lpBidLevel7Volume : Alpha 12
  askLevel8Price : Alpha 11
  bidLevel8Price : Alpha 11
  askLevel8Volume : Alpha 12
  bidLevel8Volume : Alpha 12
  lpAskLevel8Volume : Alpha 12
  lpBidLevel8Volume : Alpha 12
  askLevel9Price : Alpha 11
  bidLevel9Price : Alpha 11
  askLevel9Volume : Alpha 12
  bidLevel9Volume : Alpha 12
  lpAskLevel9Volume : Alpha 12
  lpBidLevel9Volume : Alpha 12
  askLevel10Price : Alpha 11
  bidLevel10Price : Alpha 11
  askLevel10Volume : Alpha 12
  bidLevel10Volume : Alpha 12
  lpAskLevel10Volume : Alpha 12
  lpBidLevel10Volume : Alpha 12
  totalAskVolume : Alpha 12
  totalBidVolume : Alpha 12
  estimatedTradingPrice : Alpha 11
  estimatedTradingVolume : Alpha 12
  midPrice : Alpha 11
  totalMidPriceAskVolumeTotalAskVolumeOnMidPrice : Alpha 12
  totalMidPriceBidVolumeTotalBidVolumeOnMidPrice : Alpha 12
  endKeyword : Alpha 1
  deriving DecidableEq, Repr

namespace SecuritiesQuoteMmLpQuotesIncluded10LevelMessage

def encode (message : SecuritiesQuoteMmLpQuotesIncluded10LevelMessage) : List UInt8 :=
  Alpha.encode message.messageSequenceNumber
    ++ (Alpha.encode message.boardId
    ++ (Alpha.encode message.sessionId
    ++ (Alpha.encode message.isinCode
    ++ (Alpha.encode message.aDesignatedNumberForAnIssueFromKrx
    ++ (Alpha.encode message.processingTimeOfTradingSystem
    ++ (Alpha.encode message.askLevel1Price
    ++ (Alpha.encode message.bidLevel1Price
    ++ (Alpha.encode message.askLevel1Volume
    ++ (Alpha.encode message.bidLevel1Volume
    ++ (Alpha.encode message.lpAskLevel1Volume
    ++ (Alpha.encode message.lpBidLevel1Volume
    ++ (Alpha.encode message.askLevel2Price
    ++ (Alpha.encode message.bidLevel2Price
    ++ (Alpha.encode message.askLevel2Volume
    ++ (Alpha.encode message.bidLevel2Volume
    ++ (Alpha.encode message.lpAskLevel2Volume
    ++ (Alpha.encode message.lpBidLevel2Volume
    ++ (Alpha.encode message.askLevel3Price
    ++ (Alpha.encode message.bidLevel3Price
    ++ (Alpha.encode message.askLevel3Volume
    ++ (Alpha.encode message.bidLevel3Volume
    ++ (Alpha.encode message.lpAskLevel3Volume
    ++ (Alpha.encode message.lpBidLevel3Volume
    ++ (Alpha.encode message.askLevel4Price
    ++ (Alpha.encode message.bidLevel4Price
    ++ (Alpha.encode message.askLevel4Volume
    ++ (Alpha.encode message.bidLevel4Volume
    ++ (Alpha.encode message.lpAskLevel4Volume
    ++ (Alpha.encode message.lpBidLevel4Volume
    ++ (Alpha.encode message.askLevel5Price
    ++ (Alpha.encode message.bidLevel5Price
    ++ (Alpha.encode message.askLevel5Volume
    ++ (Alpha.encode message.bidLevel5Volume
    ++ (Alpha.encode message.lpAskLevel5Volume
    ++ (Alpha.encode message.lpBidLevel5Volume
    ++ (Alpha.encode message.askLevel6Price
    ++ (Alpha.encode message.bidLevel6Price
    ++ (Alpha.encode message.askLevel6Volume
    ++ (Alpha.encode message.bidLevel6Volume
    ++ (Alpha.encode message.lpAskLevel6Volume
    ++ (Alpha.encode message.lpBidLevel6Volume
    ++ (Alpha.encode message.askLevel7Price
    ++ (Alpha.encode message.bidLevel7Price
    ++ (Alpha.encode message.askLevel7Volume
    ++ (Alpha.encode message.bidLevel7Volume
    ++ (Alpha.encode message.lpAskLevel7Volume
    ++ (Alpha.encode message.lpBidLevel7Volume
    ++ (Alpha.encode message.askLevel8Price
    ++ (Alpha.encode message.bidLevel8Price
    ++ (Alpha.encode message.askLevel8Volume
    ++ (Alpha.encode message.bidLevel8Volume
    ++ (Alpha.encode message.lpAskLevel8Volume
    ++ (Alpha.encode message.lpBidLevel8Volume
    ++ (Alpha.encode message.askLevel9Price
    ++ (Alpha.encode message.bidLevel9Price
    ++ (Alpha.encode message.askLevel9Volume
    ++ (Alpha.encode message.bidLevel9Volume
    ++ (Alpha.encode message.lpAskLevel9Volume
    ++ (Alpha.encode message.lpBidLevel9Volume
    ++ (Alpha.encode message.askLevel10Price
    ++ (Alpha.encode message.bidLevel10Price
    ++ (Alpha.encode message.askLevel10Volume
    ++ (Alpha.encode message.bidLevel10Volume
    ++ (Alpha.encode message.lpAskLevel10Volume
    ++ (Alpha.encode message.lpBidLevel10Volume
    ++ (Alpha.encode message.totalAskVolume
    ++ (Alpha.encode message.totalBidVolume
    ++ (Alpha.encode message.estimatedTradingPrice
    ++ (Alpha.encode message.estimatedTradingVolume
    ++ (Alpha.encode message.midPrice
    ++ (Alpha.encode message.totalMidPriceAskVolumeTotalAskVolumeOnMidPrice
    ++ (Alpha.encode message.totalMidPriceBidVolumeTotalBidVolumeOnMidPrice
    ++ (Alpha.encode message.endKeyword)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (SecuritiesQuoteMmLpQuotesIncluded10LevelMessage × List UInt8) := do
  let (messageSequenceNumber, bytes) ← Alpha.decode 8 bytes
  let (boardId, bytes) ← Alpha.decode 2 bytes
  let (sessionId, bytes) ← Alpha.decode 2 bytes
  let (isinCode, bytes) ← Alpha.decode 12 bytes
  let (aDesignatedNumberForAnIssueFromKrx, bytes) ← Alpha.decode 6 bytes
  let (processingTimeOfTradingSystem, bytes) ← Alpha.decode 12 bytes
  let (askLevel1Price, bytes) ← Alpha.decode 11 bytes
  let (bidLevel1Price, bytes) ← Alpha.decode 11 bytes
  let (askLevel1Volume, bytes) ← Alpha.decode 12 bytes
  let (bidLevel1Volume, bytes) ← Alpha.decode 12 bytes
  let (lpAskLevel1Volume, bytes) ← Alpha.decode 12 bytes
  let (lpBidLevel1Volume, bytes) ← Alpha.decode 12 bytes
  let (askLevel2Price, bytes) ← Alpha.decode 11 bytes
  let (bidLevel2Price, bytes) ← Alpha.decode 11 bytes
  let (askLevel2Volume, bytes) ← Alpha.decode 12 bytes
  let (bidLevel2Volume, bytes) ← Alpha.decode 12 bytes
  let (lpAskLevel2Volume, bytes) ← Alpha.decode 12 bytes
  let (lpBidLevel2Volume, bytes) ← Alpha.decode 12 bytes
  let (askLevel3Price, bytes) ← Alpha.decode 11 bytes
  let (bidLevel3Price, bytes) ← Alpha.decode 11 bytes
  let (askLevel3Volume, bytes) ← Alpha.decode 12 bytes
  let (bidLevel3Volume, bytes) ← Alpha.decode 12 bytes
  let (lpAskLevel3Volume, bytes) ← Alpha.decode 12 bytes
  let (lpBidLevel3Volume, bytes) ← Alpha.decode 12 bytes
  let (askLevel4Price, bytes) ← Alpha.decode 11 bytes
  let (bidLevel4Price, bytes) ← Alpha.decode 11 bytes
  let (askLevel4Volume, bytes) ← Alpha.decode 12 bytes
  let (bidLevel4Volume, bytes) ← Alpha.decode 12 bytes
  let (lpAskLevel4Volume, bytes) ← Alpha.decode 12 bytes
  let (lpBidLevel4Volume, bytes) ← Alpha.decode 12 bytes
  let (askLevel5Price, bytes) ← Alpha.decode 11 bytes
  let (bidLevel5Price, bytes) ← Alpha.decode 11 bytes
  let (askLevel5Volume, bytes) ← Alpha.decode 12 bytes
  let (bidLevel5Volume, bytes) ← Alpha.decode 12 bytes
  let (lpAskLevel5Volume, bytes) ← Alpha.decode 12 bytes
  let (lpBidLevel5Volume, bytes) ← Alpha.decode 12 bytes
  let (askLevel6Price, bytes) ← Alpha.decode 11 bytes
  let (bidLevel6Price, bytes) ← Alpha.decode 11 bytes
  let (askLevel6Volume, bytes) ← Alpha.decode 12 bytes
  let (bidLevel6Volume, bytes) ← Alpha.decode 12 bytes
  let (lpAskLevel6Volume, bytes) ← Alpha.decode 12 bytes
  let (lpBidLevel6Volume, bytes) ← Alpha.decode 12 bytes
  let (askLevel7Price, bytes) ← Alpha.decode 11 bytes
  let (bidLevel7Price, bytes) ← Alpha.decode 11 bytes
  let (askLevel7Volume, bytes) ← Alpha.decode 12 bytes
  let (bidLevel7Volume, bytes) ← Alpha.decode 12 bytes
  let (lpAskLevel7Volume, bytes) ← Alpha.decode 12 bytes
  let (lpBidLevel7Volume, bytes) ← Alpha.decode 12 bytes
  let (askLevel8Price, bytes) ← Alpha.decode 11 bytes
  let (bidLevel8Price, bytes) ← Alpha.decode 11 bytes
  let (askLevel8Volume, bytes) ← Alpha.decode 12 bytes
  let (bidLevel8Volume, bytes) ← Alpha.decode 12 bytes
  let (lpAskLevel8Volume, bytes) ← Alpha.decode 12 bytes
  let (lpBidLevel8Volume, bytes) ← Alpha.decode 12 bytes
  let (askLevel9Price, bytes) ← Alpha.decode 11 bytes
  let (bidLevel9Price, bytes) ← Alpha.decode 11 bytes
  let (askLevel9Volume, bytes) ← Alpha.decode 12 bytes
  let (bidLevel9Volume, bytes) ← Alpha.decode 12 bytes
  let (lpAskLevel9Volume, bytes) ← Alpha.decode 12 bytes
  let (lpBidLevel9Volume, bytes) ← Alpha.decode 12 bytes
  let (askLevel10Price, bytes) ← Alpha.decode 11 bytes
  let (bidLevel10Price, bytes) ← Alpha.decode 11 bytes
  let (askLevel10Volume, bytes) ← Alpha.decode 12 bytes
  let (bidLevel10Volume, bytes) ← Alpha.decode 12 bytes
  let (lpAskLevel10Volume, bytes) ← Alpha.decode 12 bytes
  let (lpBidLevel10Volume, bytes) ← Alpha.decode 12 bytes
  let (totalAskVolume, bytes) ← Alpha.decode 12 bytes
  let (totalBidVolume, bytes) ← Alpha.decode 12 bytes
  let (estimatedTradingPrice, bytes) ← Alpha.decode 11 bytes
  let (estimatedTradingVolume, bytes) ← Alpha.decode 12 bytes
  let (midPrice, bytes) ← Alpha.decode 11 bytes
  let (totalMidPriceAskVolumeTotalAskVolumeOnMidPrice, bytes) ← Alpha.decode 12 bytes
  let (totalMidPriceBidVolumeTotalBidVolumeOnMidPrice, bytes) ← Alpha.decode 12 bytes
  let (endKeyword, bytes) ← Alpha.decode 1 bytes
  pure ({ messageSequenceNumber, boardId, sessionId, isinCode, aDesignatedNumberForAnIssueFromKrx, processingTimeOfTradingSystem, askLevel1Price, bidLevel1Price, askLevel1Volume, bidLevel1Volume, lpAskLevel1Volume, lpBidLevel1Volume, askLevel2Price, bidLevel2Price, askLevel2Volume, bidLevel2Volume, lpAskLevel2Volume, lpBidLevel2Volume, askLevel3Price, bidLevel3Price, askLevel3Volume, bidLevel3Volume, lpAskLevel3Volume, lpBidLevel3Volume, askLevel4Price, bidLevel4Price, askLevel4Volume, bidLevel4Volume, lpAskLevel4Volume, lpBidLevel4Volume, askLevel5Price, bidLevel5Price, askLevel5Volume, bidLevel5Volume, lpAskLevel5Volume, lpBidLevel5Volume, askLevel6Price, bidLevel6Price, askLevel6Volume, bidLevel6Volume, lpAskLevel6Volume, lpBidLevel6Volume, askLevel7Price, bidLevel7Price, askLevel7Volume, bidLevel7Volume, lpAskLevel7Volume, lpBidLevel7Volume, askLevel8Price, bidLevel8Price, askLevel8Volume, bidLevel8Volume, lpAskLevel8Volume, lpBidLevel8Volume, askLevel9Price, bidLevel9Price, askLevel9Volume, bidLevel9Volume, lpAskLevel9Volume, lpBidLevel9Volume, askLevel10Price, bidLevel10Price, askLevel10Volume, bidLevel10Volume, lpAskLevel10Volume, lpBidLevel10Volume, totalAskVolume, totalBidVolume, estimatedTradingPrice, estimatedTradingVolume, midPrice, totalMidPriceAskVolumeTotalAskVolumeOnMidPrice, totalMidPriceBidVolumeTotalBidVolumeOnMidPrice, endKeyword }, bytes)

@[simp] theorem encode_length (message : SecuritiesQuoteMmLpQuotesIncluded10LevelMessage) : (encode message).length = 825 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : SecuritiesQuoteMmLpQuotesIncluded10LevelMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : SecuritiesQuoteMmLpQuotesIncluded10LevelMessage) (rest : List UInt8) :
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

end SecuritiesQuoteMmLpQuotesIncluded10LevelMessage

/-- Securities Order Filled Message: 181 bytes -/
structure SecuritiesOrderFilledMessage where
  messageSequenceNumber : Alpha 8
  boardId : Alpha 2
  sessionId : Alpha 2
  isinCode : Alpha 12
  aDesignatedNumberForAnIssueFromKrx : Alpha 6
  processingTimeOfTradingSystem : Alpha 12
  priceChangeAgainstPreviousDay : Alpha 1
  aPriceChangeAgainstThePreviousDay : Alpha 11
  tradingPrice : Alpha 11
  tradingVolume : Alpha 10
  openingPrice : Alpha 11
  todaysHigh : Alpha 11
  todaysLow : Alpha 11
  accumulatedTradingVolume : Alpha 12
  accumulatedTradingValue : Alpha 22
  finalAskBidTypeCode : Alpha 1
  lpHoldingQuantity : Alpha 15
  theBestAsk : Alpha 11
  theBestBid : Alpha 11
  endKeyword : Alpha 1
  deriving DecidableEq, Repr

namespace SecuritiesOrderFilledMessage

def encode (message : SecuritiesOrderFilledMessage) : List UInt8 :=
  Alpha.encode message.messageSequenceNumber
    ++ (Alpha.encode message.boardId
    ++ (Alpha.encode message.sessionId
    ++ (Alpha.encode message.isinCode
    ++ (Alpha.encode message.aDesignatedNumberForAnIssueFromKrx
    ++ (Alpha.encode message.processingTimeOfTradingSystem
    ++ (Alpha.encode message.priceChangeAgainstPreviousDay
    ++ (Alpha.encode message.aPriceChangeAgainstThePreviousDay
    ++ (Alpha.encode message.tradingPrice
    ++ (Alpha.encode message.tradingVolume
    ++ (Alpha.encode message.openingPrice
    ++ (Alpha.encode message.todaysHigh
    ++ (Alpha.encode message.todaysLow
    ++ (Alpha.encode message.accumulatedTradingVolume
    ++ (Alpha.encode message.accumulatedTradingValue
    ++ (Alpha.encode message.finalAskBidTypeCode
    ++ (Alpha.encode message.lpHoldingQuantity
    ++ (Alpha.encode message.theBestAsk
    ++ (Alpha.encode message.theBestBid
    ++ (Alpha.encode message.endKeyword)))))))))))))))))))

def decode (bytes : List UInt8) : Option (SecuritiesOrderFilledMessage × List UInt8) := do
  let (messageSequenceNumber, bytes) ← Alpha.decode 8 bytes
  let (boardId, bytes) ← Alpha.decode 2 bytes
  let (sessionId, bytes) ← Alpha.decode 2 bytes
  let (isinCode, bytes) ← Alpha.decode 12 bytes
  let (aDesignatedNumberForAnIssueFromKrx, bytes) ← Alpha.decode 6 bytes
  let (processingTimeOfTradingSystem, bytes) ← Alpha.decode 12 bytes
  let (priceChangeAgainstPreviousDay, bytes) ← Alpha.decode 1 bytes
  let (aPriceChangeAgainstThePreviousDay, bytes) ← Alpha.decode 11 bytes
  let (tradingPrice, bytes) ← Alpha.decode 11 bytes
  let (tradingVolume, bytes) ← Alpha.decode 10 bytes
  let (openingPrice, bytes) ← Alpha.decode 11 bytes
  let (todaysHigh, bytes) ← Alpha.decode 11 bytes
  let (todaysLow, bytes) ← Alpha.decode 11 bytes
  let (accumulatedTradingVolume, bytes) ← Alpha.decode 12 bytes
  let (accumulatedTradingValue, bytes) ← Alpha.decode 22 bytes
  let (finalAskBidTypeCode, bytes) ← Alpha.decode 1 bytes
  let (lpHoldingQuantity, bytes) ← Alpha.decode 15 bytes
  let (theBestAsk, bytes) ← Alpha.decode 11 bytes
  let (theBestBid, bytes) ← Alpha.decode 11 bytes
  let (endKeyword, bytes) ← Alpha.decode 1 bytes
  pure ({ messageSequenceNumber, boardId, sessionId, isinCode, aDesignatedNumberForAnIssueFromKrx, processingTimeOfTradingSystem, priceChangeAgainstPreviousDay, aPriceChangeAgainstThePreviousDay, tradingPrice, tradingVolume, openingPrice, todaysHigh, todaysLow, accumulatedTradingVolume, accumulatedTradingValue, finalAskBidTypeCode, lpHoldingQuantity, theBestAsk, theBestBid, endKeyword }, bytes)

@[simp] theorem encode_length (message : SecuritiesOrderFilledMessage) : (encode message).length = 181 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : SecuritiesOrderFilledMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SecuritiesOrderFilledMessage) (rest : List UInt8) :
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
  rw [Alpha.decode_encode, some_bind]
  rfl

end SecuritiesOrderFilledMessage

/-- Market Operation Ts Message: 63 bytes -/
structure MarketOperationTsMessage where
  messageSequenceNumber : Alpha 8
  boardId : Alpha 2
  sessionId : Alpha 2
  isinCode : Alpha 12
  aDesignatedNumberForAnIssueFromKrx : Alpha 6
  processingTimeOfTradingSystem : Alpha 12
  boardEventId : Alpha 3
  startTimeOfABoardEvent : Alpha 9
  boardEventGroupCode : Alpha 5
  tradingHaltReasonCode : Alpha 3
  endKeyword : Alpha 1
  deriving DecidableEq, Repr

namespace MarketOperationTsMessage

def encode (message : MarketOperationTsMessage) : List UInt8 :=
  Alpha.encode message.messageSequenceNumber
    ++ (Alpha.encode message.boardId
    ++ (Alpha.encode message.sessionId
    ++ (Alpha.encode message.isinCode
    ++ (Alpha.encode message.aDesignatedNumberForAnIssueFromKrx
    ++ (Alpha.encode message.processingTimeOfTradingSystem
    ++ (Alpha.encode message.boardEventId
    ++ (Alpha.encode message.startTimeOfABoardEvent
    ++ (Alpha.encode message.boardEventGroupCode
    ++ (Alpha.encode message.tradingHaltReasonCode
    ++ (Alpha.encode message.endKeyword))))))))))

def decode (bytes : List UInt8) : Option (MarketOperationTsMessage × List UInt8) := do
  let (messageSequenceNumber, bytes) ← Alpha.decode 8 bytes
  let (boardId, bytes) ← Alpha.decode 2 bytes
  let (sessionId, bytes) ← Alpha.decode 2 bytes
  let (isinCode, bytes) ← Alpha.decode 12 bytes
  let (aDesignatedNumberForAnIssueFromKrx, bytes) ← Alpha.decode 6 bytes
  let (processingTimeOfTradingSystem, bytes) ← Alpha.decode 12 bytes
  let (boardEventId, bytes) ← Alpha.decode 3 bytes
  let (startTimeOfABoardEvent, bytes) ← Alpha.decode 9 bytes
  let (boardEventGroupCode, bytes) ← Alpha.decode 5 bytes
  let (tradingHaltReasonCode, bytes) ← Alpha.decode 3 bytes
  let (endKeyword, bytes) ← Alpha.decode 1 bytes
  pure ({ messageSequenceNumber, boardId, sessionId, isinCode, aDesignatedNumberForAnIssueFromKrx, processingTimeOfTradingSystem, boardEventId, startTimeOfABoardEvent, boardEventGroupCode, tradingHaltReasonCode, endKeyword }, bytes)

@[simp] theorem encode_length (message : MarketOperationTsMessage) : (encode message).length = 63 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : MarketOperationTsMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MarketOperationTsMessage) (rest : List UInt8) :
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

end MarketOperationTsMessage

/-- Issue Closing Message: 107 bytes -/
structure IssueClosingMessage where
  messageSequenceNumber : Alpha 8
  boardId : Alpha 2
  isinCode : Alpha 12
  aDesignatedNumberForAnIssueFromKrx : Alpha 6
  closingPrice : Alpha 11
  closingPriceTypeCode : Alpha 1
  upperLimitPriceOnTheSinglePriceTradeInTheOffHoursSession : Alpha 11
  lowerLimitPriceOnTheSinglePriceTradeInTheOffHoursSession : Alpha 11
  closingPriceWeightedStockPriceAverage : Alpha 11
  closingPriceBasePriceOfBuyIn : Alpha 11
  closingPriceUpperLimitOfBuyIn : Alpha 11
  closingPriceLowerLimitOfBuyIn : Alpha 11
  endKeyword : Alpha 1
  deriving DecidableEq, Repr

namespace IssueClosingMessage

def encode (message : IssueClosingMessage) : List UInt8 :=
  Alpha.encode message.messageSequenceNumber
    ++ (Alpha.encode message.boardId
    ++ (Alpha.encode message.isinCode
    ++ (Alpha.encode message.aDesignatedNumberForAnIssueFromKrx
    ++ (Alpha.encode message.closingPrice
    ++ (Alpha.encode message.closingPriceTypeCode
    ++ (Alpha.encode message.upperLimitPriceOnTheSinglePriceTradeInTheOffHoursSession
    ++ (Alpha.encode message.lowerLimitPriceOnTheSinglePriceTradeInTheOffHoursSession
    ++ (Alpha.encode message.closingPriceWeightedStockPriceAverage
    ++ (Alpha.encode message.closingPriceBasePriceOfBuyIn
    ++ (Alpha.encode message.closingPriceUpperLimitOfBuyIn
    ++ (Alpha.encode message.closingPriceLowerLimitOfBuyIn
    ++ (Alpha.encode message.endKeyword))))))))))))

def decode (bytes : List UInt8) : Option (IssueClosingMessage × List UInt8) := do
  let (messageSequenceNumber, bytes) ← Alpha.decode 8 bytes
  let (boardId, bytes) ← Alpha.decode 2 bytes
  let (isinCode, bytes) ← Alpha.decode 12 bytes
  let (aDesignatedNumberForAnIssueFromKrx, bytes) ← Alpha.decode 6 bytes
  let (closingPrice, bytes) ← Alpha.decode 11 bytes
  let (closingPriceTypeCode, bytes) ← Alpha.decode 1 bytes
  let (upperLimitPriceOnTheSinglePriceTradeInTheOffHoursSession, bytes) ← Alpha.decode 11 bytes
  let (lowerLimitPriceOnTheSinglePriceTradeInTheOffHoursSession, bytes) ← Alpha.decode 11 bytes
  let (closingPriceWeightedStockPriceAverage, bytes) ← Alpha.decode 11 bytes
  let (closingPriceBasePriceOfBuyIn, bytes) ← Alpha.decode 11 bytes
  let (closingPriceUpperLimitOfBuyIn, bytes) ← Alpha.decode 11 bytes
  let (closingPriceLowerLimitOfBuyIn, bytes) ← Alpha.decode 11 bytes
  let (endKeyword, bytes) ← Alpha.decode 1 bytes
  pure ({ messageSequenceNumber, boardId, isinCode, aDesignatedNumberForAnIssueFromKrx, closingPrice, closingPriceTypeCode, upperLimitPriceOnTheSinglePriceTradeInTheOffHoursSession, lowerLimitPriceOnTheSinglePriceTradeInTheOffHoursSession, closingPriceWeightedStockPriceAverage, closingPriceBasePriceOfBuyIn, closingPriceUpperLimitOfBuyIn, closingPriceLowerLimitOfBuyIn, endKeyword }, bytes)

@[simp] theorem encode_length (message : IssueClosingMessage) : (encode message).length = 107 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : IssueClosingMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : IssueClosingMessage) (rest : List UInt8) :
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

end IssueClosingMessage

/-- Triggering Removing Vi Message: 111 bytes -/
structure TriggeringRemovingViMessage where
  messageSequenceNumber : Alpha 8
  boardId : Alpha 2
  isinCode : Alpha 12
  aDesignatedNumberForAnIssueFromKrx : Alpha 6
  processingTimeOfTradingSystem : Alpha 12
  theTimeEndingVi : Alpha 9
  viStatusCode : Alpha 1
  viTypeCode : Alpha 1
  aBasePriceToTriggerStaticVi : Alpha 11
  aBasePriceToTriggerDynamicVi : Alpha 11
  viTriggeringPrice : Alpha 11
  disparateRatioToTriggerStaticVi : Alpha 13
  disparateRatioToTriggerDynamicVi : Alpha 13
  endKeyword : Alpha 1
  deriving DecidableEq, Repr

namespace TriggeringRemovingViMessage

def encode (message : TriggeringRemovingViMessage) : List UInt8 :=
  Alpha.encode message.messageSequenceNumber
    ++ (Alpha.encode message.boardId
    ++ (Alpha.encode message.isinCode
    ++ (Alpha.encode message.aDesignatedNumberForAnIssueFromKrx
    ++ (Alpha.encode message.processingTimeOfTradingSystem
    ++ (Alpha.encode message.theTimeEndingVi
    ++ (Alpha.encode message.viStatusCode
    ++ (Alpha.encode message.viTypeCode
    ++ (Alpha.encode message.aBasePriceToTriggerStaticVi
    ++ (Alpha.encode message.aBasePriceToTriggerDynamicVi
    ++ (Alpha.encode message.viTriggeringPrice
    ++ (Alpha.encode message.disparateRatioToTriggerStaticVi
    ++ (Alpha.encode message.disparateRatioToTriggerDynamicVi
    ++ (Alpha.encode message.endKeyword)))))))))))))

def decode (bytes : List UInt8) : Option (TriggeringRemovingViMessage × List UInt8) := do
  let (messageSequenceNumber, bytes) ← Alpha.decode 8 bytes
  let (boardId, bytes) ← Alpha.decode 2 bytes
  let (isinCode, bytes) ← Alpha.decode 12 bytes
  let (aDesignatedNumberForAnIssueFromKrx, bytes) ← Alpha.decode 6 bytes
  let (processingTimeOfTradingSystem, bytes) ← Alpha.decode 12 bytes
  let (theTimeEndingVi, bytes) ← Alpha.decode 9 bytes
  let (viStatusCode, bytes) ← Alpha.decode 1 bytes
  let (viTypeCode, bytes) ← Alpha.decode 1 bytes
  let (aBasePriceToTriggerStaticVi, bytes) ← Alpha.decode 11 bytes
  let (aBasePriceToTriggerDynamicVi, bytes) ← Alpha.decode 11 bytes
  let (viTriggeringPrice, bytes) ← Alpha.decode 11 bytes
  let (disparateRatioToTriggerStaticVi, bytes) ← Alpha.decode 13 bytes
  let (disparateRatioToTriggerDynamicVi, bytes) ← Alpha.decode 13 bytes
  let (endKeyword, bytes) ← Alpha.decode 1 bytes
  pure ({ messageSequenceNumber, boardId, isinCode, aDesignatedNumberForAnIssueFromKrx, processingTimeOfTradingSystem, theTimeEndingVi, viStatusCode, viTypeCode, aBasePriceToTriggerStaticVi, aBasePriceToTriggerDynamicVi, viTriggeringPrice, disparateRatioToTriggerStaticVi, disparateRatioToTriggerDynamicVi, endKeyword }, bytes)

@[simp] theorem encode_length (message : TriggeringRemovingViMessage) : (encode message).length = 111 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : TriggeringRemovingViMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TriggeringRemovingViMessage) (rest : List UInt8) :
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

end TriggeringRemovingViMessage

/-- Closing Price Trading Quote Message: 53 bytes -/
structure ClosingPriceTradingQuoteMessage where
  messageSequenceNumber : Alpha 8
  boardId : Alpha 2
  isinCode : Alpha 12
  aDesignatedNumberForAnIssueFromKrx : Alpha 6
  totalAskVolume : Alpha 12
  totalBidVolume : Alpha 12
  endKeyword : Alpha 1
  deriving DecidableEq, Repr

namespace ClosingPriceTradingQuoteMessage

def encode (message : ClosingPriceTradingQuoteMessage) : List UInt8 :=
  Alpha.encode message.messageSequenceNumber
    ++ (Alpha.encode message.boardId
    ++ (Alpha.encode message.isinCode
    ++ (Alpha.encode message.aDesignatedNumberForAnIssueFromKrx
    ++ (Alpha.encode message.totalAskVolume
    ++ (Alpha.encode message.totalBidVolume
    ++ (Alpha.encode message.endKeyword))))))

def decode (bytes : List UInt8) : Option (ClosingPriceTradingQuoteMessage × List UInt8) := do
  let (messageSequenceNumber, bytes) ← Alpha.decode 8 bytes
  let (boardId, bytes) ← Alpha.decode 2 bytes
  let (isinCode, bytes) ← Alpha.decode 12 bytes
  let (aDesignatedNumberForAnIssueFromKrx, bytes) ← Alpha.decode 6 bytes
  let (totalAskVolume, bytes) ← Alpha.decode 12 bytes
  let (totalBidVolume, bytes) ← Alpha.decode 12 bytes
  let (endKeyword, bytes) ← Alpha.decode 1 bytes
  pure ({ messageSequenceNumber, boardId, isinCode, aDesignatedNumberForAnIssueFromKrx, totalAskVolume, totalBidVolume, endKeyword }, bytes)

@[simp] theorem encode_length (message : ClosingPriceTradingQuoteMessage) : (encode message).length = 53 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : ClosingPriceTradingQuoteMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ClosingPriceTradingQuoteMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end ClosingPriceTradingQuoteMessage

/-- Any Payload, selected by TR Code -/
inductive Payload where
  | pollingDataMessage (message : PollingDataMessage) -- "I2500" 0x4932353030
  | securitiesQuoteMmLpQuotesIncluded10LevelMessage (message : SecuritiesQuoteMmLpQuotesIncluded10LevelMessage) -- "B753S" 0x4237353353
  | securitiesOrderFilledMessage (message : SecuritiesOrderFilledMessage) -- "A353S" 0x4133353353
  | marketOperationTsMessage (message : MarketOperationTsMessage) -- "A753S" 0x4137353353
  | issueClosingMessage (message : IssueClosingMessage) -- "A653S" 0x4136353353
  | triggeringRemovingViMessage (message : TriggeringRemovingViMessage) -- "R853S" 0x5238353353
  | closingPriceTradingQuoteMessage (message : ClosingPriceTradingQuoteMessage) -- "E153S" 0x4531353353
  deriving DecidableEq, Repr

namespace Payload

/-- The TR Code each message is sent under -/
def tag : Payload → BitVec 40
  | .pollingDataMessage _ => 314374959152
  | .securitiesQuoteMmLpQuotesIncluded10LevelMessage _ => 284394074963
  | .securitiesOrderFilledMessage _ => 280031998803
  | .marketOperationTsMessage _ => 280099107667
  | .issueClosingMessage _ => 280082330451
  | .triggeringRemovingViMessage _ => 353130328915
  | .closingPriceTradingQuoteMessage _ => 297178313555

def encode : Payload → List UInt8
  | .pollingDataMessage message => PollingDataMessage.encode message
  | .securitiesQuoteMmLpQuotesIncluded10LevelMessage message => SecuritiesQuoteMmLpQuotesIncluded10LevelMessage.encode message
  | .securitiesOrderFilledMessage message => SecuritiesOrderFilledMessage.encode message
  | .marketOperationTsMessage message => MarketOperationTsMessage.encode message
  | .issueClosingMessage message => IssueClosingMessage.encode message
  | .triggeringRemovingViMessage message => TriggeringRemovingViMessage.encode message
  | .closingPriceTradingQuoteMessage message => ClosingPriceTradingQuoteMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : Payload) : (encode message).length ≤ 825 := by
  cases message with
  | pollingDataMessage inner =>
    simp only [encode, PollingDataMessage.encode_length]
    omega
  | securitiesQuoteMmLpQuotesIncluded10LevelMessage inner =>
    simp only [encode, SecuritiesQuoteMmLpQuotesIncluded10LevelMessage.encode_length]
    omega
  | securitiesOrderFilledMessage inner =>
    simp only [encode, SecuritiesOrderFilledMessage.encode_length]
    omega
  | marketOperationTsMessage inner =>
    simp only [encode, MarketOperationTsMessage.encode_length]
    omega
  | issueClosingMessage inner =>
    simp only [encode, IssueClosingMessage.encode_length]
    omega
  | triggeringRemovingViMessage inner =>
    simp only [encode, TriggeringRemovingViMessage.encode_length]
    omega
  | closingPriceTradingQuoteMessage inner =>
    simp only [encode, ClosingPriceTradingQuoteMessage.encode_length]
    omega

def decode (tag : BitVec 40) (bytes : List UInt8) : Option (Payload × List UInt8) :=
  if tag = 314374959152 then (PollingDataMessage.decode bytes).map fun (message, rest) => (.pollingDataMessage message, rest)
  else if tag = 284394074963 then (SecuritiesQuoteMmLpQuotesIncluded10LevelMessage.decode bytes).map fun (message, rest) => (.securitiesQuoteMmLpQuotesIncluded10LevelMessage message, rest)
  else if tag = 280031998803 then (SecuritiesOrderFilledMessage.decode bytes).map fun (message, rest) => (.securitiesOrderFilledMessage message, rest)
  else if tag = 280099107667 then (MarketOperationTsMessage.decode bytes).map fun (message, rest) => (.marketOperationTsMessage message, rest)
  else if tag = 280082330451 then (IssueClosingMessage.decode bytes).map fun (message, rest) => (.issueClosingMessage message, rest)
  else if tag = 353130328915 then (TriggeringRemovingViMessage.decode bytes).map fun (message, rest) => (.triggeringRemovingViMessage message, rest)
  else if tag = 297178313555 then (ClosingPriceTradingQuoteMessage.decode bytes).map fun (message, rest) => (.closingPriceTradingQuoteMessage message, rest)
  else none

@[simp] theorem decode_encode (message : Payload) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end Payload

/-- Packet -/
structure Packet where
  payload : Payload
  deriving DecidableEq, Repr

namespace Packet

def encode (message : Packet) : List UInt8 :=
  encodeUInt 5 (Payload.tag message.payload)
    ++ (Payload.encode message.payload)

def decode (bytes : List UInt8) : Option (Packet × List UInt8) := do
  let (trCode, bytes) ← decodeUInt 5 bytes
  let (payload, bytes) ← Payload.decode trCode bytes
  pure ({ payload }, bytes)

theorem encode_length_pos (message : Packet) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : Packet) : (encode message).length ≤ 830 := by
  unfold encode
  cases message.payload with
  | pollingDataMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, PollingDataMessage.encode_length]
    omega
  | securitiesQuoteMmLpQuotesIncluded10LevelMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, SecuritiesQuoteMmLpQuotesIncluded10LevelMessage.encode_length]
    omega
  | securitiesOrderFilledMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, SecuritiesOrderFilledMessage.encode_length]
    omega
  | marketOperationTsMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, MarketOperationTsMessage.encode_length]
    omega
  | issueClosingMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, IssueClosingMessage.encode_length]
    omega
  | triggeringRemovingViMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, TriggeringRemovingViMessage.encode_length]
    omega
  | closingPriceTradingQuoteMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, ClosingPriceTradingQuoteMessage.encode_length]
    omega

@[simp] theorem decode_encode (message : Packet) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Payload.decode_encode, some_bind]
  rfl

end Packet

end Omi.NextradeNextradeEtp10levelNxtasciiV212
