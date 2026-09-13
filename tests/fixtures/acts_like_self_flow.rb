# typed: true

class Object
  def acts_like?(duck)
    respond_to?("acts_like_#{duck}?")
  end
end

module ActsLikeSelfFlow
  def converted
    time = acts_like?(:time) ? self : nil
    time_with_zone(time)
  end

  private

  def time_with_zone(time)
    if time
      time.to_time
    else
      to_time(:utc)
    end
  end
end

class ActsLikeDate
  include ActsLikeSelfFlow

  def to_time(form = :local)
    "date"
  end
end

class ActsLikeTime
  include ActsLikeSelfFlow

  def acts_like_time?
    true
  end

  def to_time
    "time"
  end
end

T.reveal_type(ActsLikeDate.new.converted) # note: String
T.reveal_type(ActsLikeTime.new.converted) # note: String
