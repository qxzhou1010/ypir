/*
 * @Description: 
 * @Author: Qixian Zhou
 * @Date: 2023-11-16 16:53:31
 */


pub mod aligned_memory;
pub mod arith;
pub mod discrete_gaussian;
pub mod noise_estimate;
pub mod number_theory;
pub mod util;

pub mod gadget;
pub mod ntt;
pub mod params;
pub mod poly;

pub mod client;
pub mod key_value;


// use rayon::prelude::*;

// #[cfg(feature = "server")]
pub mod server;
