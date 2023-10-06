#pragma once

#include <cstdlib>
#include <iosfwd>
#include <string>
#include <tuple>
#include <vector>

struct big_integer {
public:
  big_integer();
  big_integer(const big_integer& other);

  big_integer(int a);

  big_integer(long a);

  big_integer(long long a);

  big_integer(unsigned int a);

  big_integer(unsigned long a);

  big_integer(unsigned long long a);

  explicit big_integer(const std::string& str);
  ~big_integer();

  void swap(big_integer& other) noexcept {
    std::swap(digits_, other.digits_);
    std::swap(is_neg, other.is_neg);
  }

  big_integer& operator=(const big_integer& other);

  big_integer& operator+=(const big_integer& rhs);
  big_integer& operator-=(const big_integer& rhs);
  big_integer& operator*=(const big_integer& rhs);
  big_integer& operator/=(const big_integer& rhs);
  big_integer& operator%=(const big_integer& rhs);

  big_integer& operator&=(const big_integer& rhs);
  big_integer& operator|=(const big_integer& rhs);
  big_integer& operator^=(const big_integer& rhs);

  big_integer& operator<<=(int rhs);
  big_integer& operator>>=(int rhs);

  big_integer operator+() const;
  big_integer operator-() const;
  big_integer operator~() const;

  big_integer& operator++();
  big_integer operator++(int);

  big_integer& operator--();
  big_integer operator--(int);

  friend std::pair<big_integer, big_integer> longdivide(big_integer& left, const big_integer& rhs);

  friend bool operator==(const big_integer& a, const big_integer& b);
  friend bool operator!=(const big_integer& a, const big_integer& b);
  friend bool operator<(const big_integer& a, const big_integer& b);
  friend bool operator>(const big_integer& a, const big_integer& b);
  friend bool operator<=(const big_integer& a, const big_integer& b);
  friend bool operator>=(const big_integer& a, const big_integer& b);

  friend std::string to_string(const big_integer& a);

private:
  std::vector<uint32_t> digits_;
  bool is_neg = false;
  static const uint64_t base = 4294967296;
  static const uint32_t taked_digits = 1'000'000'000;

  template <typename T>
  void numeric_constructor(T number) {
    bool need_sub = true;
    if (std::numeric_limits<T>::max() == number) {
      need_sub = false;
    } else {
      number++;
    }
    if (number <= 0) {
      is_neg = true;
      number *= -1;
    }
    while (number != 0) {
      digits_.push_back(number % base);
      number /= base;
    }
    if (need_sub) {
      sub_big_small(1);
    }
  }

  void mul_big_small(uint32_t small) {
    uint64_t intermediate = 0;
    for (std::size_t i = 0; i < digits_.size(); i++) {
      intermediate += digits_[i] * static_cast<uint64_t>(small);
      digits_[i] = intermediate % base;
      intermediate /= base;
    }
    digits_.push_back(intermediate);
    clean_zeros();
  }

  void clean_zeros() {
    while (!digits_.empty() && digits_.back() == 0) {
      digits_.pop_back();
    }
  }

  void add_zeros(big_integer& big, std::size_t size) {
    if (big.digits_.size() < size) {
      big.digits_.resize(size, 0);
    }
  }

  void sub_by_modules(const big_integer& minuend, const big_integer& subtrahend) {
    uint64_t borrow = 0;
    uint32_t current_digit;
    add_zeros(*this, minuend.digits_.size());
    for (std::size_t index = 0; index < minuend.digits_.size(); index++) {
      current_digit = index >= subtrahend.digits_.size() ? 0 : subtrahend.digits_[index];
      if (borrow + current_digit > minuend.digits_[index]) {
        digits_[index] = base + minuend.digits_[index] - (borrow + current_digit);
        borrow = 1;
      } else {
        digits_[index] = minuend.digits_[index] - (borrow + current_digit);
        borrow = 0;
      }
    }
    clean_zeros();
    if (digits_.empty()) {
      is_neg = false;
    }
  }

  void add_big_small(uint32_t small) {
    if (is_neg) {
      is_neg = false;
      sub_big_small(small);
      if (!digits_.empty()) {
        is_neg = true;
      }
      return;
    }
    uint64_t carry = small;
    for (std::size_t i = 0; i < digits_.size() && carry > 0; i++) {
      carry += digits_[i];
      digits_[i] = carry % base;
      carry /= base;
    }
    digits_.push_back(carry);
    clean_zeros();
  }

  void sub_big_small(uint32_t small) {
    if (digits_.empty()) {
      is_neg = true;
      digits_.push_back(0);
    } else if (digits_.size() == 1 && digits_[0] == 0) {
      is_neg = true;
    }
    if (is_neg) {
      is_neg = false;
      add_big_small(1);
      is_neg = true;
      return;
    }
    uint64_t borrow = small;
    for (std::size_t i = 0; i < digits_.size() && borrow > 0; i++) {
      if (digits_[i] >= borrow) {
        digits_[i] -= borrow;
        borrow = 0;
      } else {
        digits_[i] = base + digits_[i] - borrow;
        borrow = 1;
      }
    }
    clean_zeros();
  }

  std::pair<uint32_t, uint32_t> bit_transform(uint32_t cur_digit, uint32_t carry) const {
    cur_digit = ~cur_digit;
    uint64_t current_result = static_cast<uint64_t>(carry) + cur_digit;
    return std::make_pair(current_result % base, current_result / base);
  }

  std::pair<uint32_t, uint32_t> return_digit(uint32_t cur_digit, uint32_t carry, bool neg) const {
    if (neg) {
      std::tie(cur_digit, carry) = bit_transform(cur_digit, carry);
    }
    return std::make_pair(cur_digit, carry);
  }

  std::pair<uint32_t, uint32_t> transform_back(uint32_t cur_digit, uint32_t borrow, bool neg) const {
    if (neg) {
      if (cur_digit < borrow) {
        cur_digit = base - borrow;
        borrow = 1;
      } else {
        cur_digit -= borrow;
        borrow = 0;
      }
      cur_digit = ~cur_digit;
    }
    return std::make_pair(cur_digit, borrow);
  }

  uint32_t normalize() {
    uint32_t ch = ((1 << 31) + digits_.back() - 1) / digits_.back();
    mul_big_small(ch);
    return ch;
  }

  uint64_t div_big_small(uint32_t small) {
    uint64_t carry = 0;
    for (std::reverse_iterator index = digits_.rbegin(); index != digits_.rend(); index++) {
      carry = carry * big_integer::base + *index;
      *index = carry / small;
      carry %= small;
    }
    clean_zeros();
    return carry;
  }
};

big_integer operator+(const big_integer& a, const big_integer& b);
big_integer operator-(const big_integer& a, const big_integer& b);
big_integer operator*(const big_integer& a, const big_integer& b);
big_integer operator/(const big_integer& a, const big_integer& b);
big_integer operator%(const big_integer& a, const big_integer& b);

big_integer operator&(const big_integer& a, const big_integer& b);
big_integer operator|(const big_integer& a, const big_integer& b);
big_integer operator^(const big_integer& a, const big_integer& b);

big_integer operator<<(const big_integer& a, int b);
big_integer operator>>(const big_integer& a, int b);

bool operator==(const big_integer& a, const big_integer& b);
bool operator!=(const big_integer& a, const big_integer& b);
bool operator<(const big_integer& a, const big_integer& b);
bool operator>(const big_integer& a, const big_integer& b);
bool operator<=(const big_integer& a, const big_integer& b);
bool operator>=(const big_integer& a, const big_integer& b);

std::string to_string(const big_integer& a);
std::ostream& operator<<(std::ostream& out, const big_integer& a);