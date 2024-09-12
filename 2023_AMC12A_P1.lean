import Mathlib.data.real.basic

-- Define the speeds and the initial distance between the cities
def speed_alicia : ℝ := 18  -- miles per hour
def speed_beth : ℝ := 12    -- miles per hour
def distance_between_cities : ℝ := 45 -- miles

-- Define the time when Alicia and Beth meet
def time_to_meet : ℝ :=
  distance_between_cities / (speed_alicia + speed_beth)

-- Calculate the distance Alicia has traveled when they meet
def distance_alicia_traveled : ℝ :=
  speed_alicia * time_to_meet

-- Prove that Alicia has traveled 27 miles when they meet
theorem distance_alicia_traveled_is_27 : distance_alicia_traveled = 27 :=
begin
  -- Calculate the time to meet
  have h_time_to_meet : time_to_meet = distance_between_cities / (speed_alicia + speed_beth),
  { rfl },

  -- Calculate the distance Alicia has traveled
  calc
    distance_alicia_traveled
      = speed_alicia * time_to_meet : rfl
  ... = speed_alicia * (distance_between_cities / (speed_alicia + speed_beth)) : by rw h_time_to_meet
  ... = 18 * (45 / (18 + 12)) : rfl
  ... = 18 * (45 / 30) : by simp
  ... = 18 * 1.5 : by simp
  ... = 27 : by simp
end
