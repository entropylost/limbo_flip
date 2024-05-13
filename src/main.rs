use std::{
    f32::consts::TAU,
    ops::{Add, AddAssign, Div, Index, IndexMut, Mul},
    time::Instant,
};

use ::rand::{random, seq::SliceRandom, thread_rng};
use macroquad::prelude::*;
use smallvec::SmallVec;

#[allow(non_upper_case_globals)]
const gravity: Vec2 = Vec2::new(0.0, -1.0);
#[allow(non_upper_case_globals)]
const particle_radius: f32 = 0.3;
#[allow(non_upper_case_globals)]
const dt: f32 = 1.0 / 60.0;

#[derive(Debug, Clone)]
struct Grid<T> {
    data: Vec<T>,
    size: IVec2,
    offset: IVec2,
    frac_offset: Vec2,
    default: T,
}
impl<T> Index<IVec2> for Grid<T> {
    type Output = T;

    fn index(&self, index: IVec2) -> &Self::Output {
        let index = index - self.offset;
        if index.x < 0 || index.y < 0 || index.x >= self.size.x || index.y >= self.size.y {
            return &self.default;
        }
        &self.data[(index.x + index.y * self.size.x) as usize]
    }
}
impl<T> IndexMut<IVec2> for Grid<T> {
    fn index_mut(&mut self, index: IVec2) -> &mut Self::Output {
        let index = index - self.offset;
        if index.x < 0 || index.y < 0 || index.x >= self.size.x || index.y >= self.size.y {
            panic!("Index out of bounds");
        }
        &mut self.data[(index.x + index.y * self.size.x) as usize]
    }
}
impl<T: Clone> Grid<T> {
    fn with_offset(size: IVec2, offset: Vec2, default: T) -> Self {
        Self {
            data: vec![default.clone(); (size.x * size.y) as usize],
            size,
            offset: offset.floor().as_ivec2(),
            frac_offset: offset.fract(),
            default,
        }
    }
    fn new(size: IVec2, default: T) -> Self {
        Self::with_offset(size, Vec2::ZERO, default)
    }
    fn from_fn_offset(
        size: IVec2,
        offset: Vec2,
        default: T,
        mut f: impl FnMut(IVec2) -> T,
    ) -> Self {
        let frac_offset = offset.fract();
        let offset = offset.floor().as_ivec2();
        let mut data = Vec::with_capacity((size.x * size.y) as usize);
        for y in 0..size.y {
            for x in 0..size.x {
                let pos = IVec2::new(x, y) + offset;
                data.push(f(pos));
            }
        }
        Self {
            data,
            size,
            offset,
            frac_offset,
            default,
        }
    }
    fn load_fn(&mut self, mut f: impl FnMut(IVec2) -> T) {
        for y in 0..self.size.y {
            for x in 0..self.size.x {
                let pos = IVec2::new(x, y) + self.offset;
                self[pos] = f(pos);
            }
        }
    }
    fn set(&mut self, value: T) {
        for x in &mut self.data {
            *x = value.clone();
        }
    }
    fn map(&self, mut f: impl FnMut(IVec2, T) -> T) -> Self {
        let mut result = self.clone();
        for y in 0..self.size.y {
            for x in 0..self.size.x {
                let pos = IVec2::new(x, y) + self.offset;
                result[pos] = f(pos, self[pos].clone());
            }
        }
        result
    }
    fn map2<S>(&self, other: &Grid<S>, mut f: impl FnMut(IVec2, T, S) -> T) -> Self
    where
        S: Clone,
    {
        let mut result = self.clone();
        for y in 0..self.size.y {
            for x in 0..self.size.x {
                let pos = IVec2::new(x, y) + self.offset;
                result[pos] = f(pos, self[pos].clone(), other[pos].clone());
            }
        }
        result
    }
    fn foreach(&self, mut f: impl FnMut(IVec2, T)) {
        for y in 0..self.size.y {
            for x in 0..self.size.x {
                let pos = IVec2::new(x, y) + self.offset;
                f(pos, self[pos].clone());
            }
        }
    }
}
impl<T: Add<Output = T> + Mul<f32, Output = T> + Clone> Grid<T> {
    fn sample_reject(&self, pos: Vec2, mut reject: impl FnMut(&Self, IVec2) -> bool) -> T
    where
        T: Div<f32, Output = T> + Default,
    {
        let mut accept = |grid: &Grid<T>, pos: IVec2| !reject(grid, pos) as u32 as f32;
        fn mul_void<T: Default + Clone + Mul<f32, Output = T>>(x: &T, y: f32) -> T {
            if y == 0.0 {
                T::default()
            } else {
                x.clone() * y
            }
        }
        let pos = pos - self.frac_offset;
        let p00 = pos.floor().as_ivec2();
        let p10 = p00 + IVec2::X;
        let p01 = p00 + IVec2::Y;
        let p11 = p00 + IVec2::ONE;
        let f = pos.fract();
        let w00 = (1.0 - f.x) * (1.0 - f.y) * accept(self, p00);
        let w10 = f.x * (1.0 - f.y) * accept(self, p10);
        let w01 = (1.0 - f.x) * f.y * accept(self, p01);
        let w11 = f.x * f.y * accept(self, p11);
        (mul_void(&self[p00], w00)
            + mul_void(&self[p10], w10)
            + mul_void(&self[p01], w01)
            + mul_void(&self[p11], w11))
            / (w00 + w10 + w01 + w11)
    }
    fn sample(&self, pos: Vec2) -> T {
        let pos = pos - self.frac_offset;
        let p00 = pos.floor().as_ivec2();
        let p10 = p00 + IVec2::X;
        let p01 = p00 + IVec2::Y;
        let p11 = p00 + IVec2::ONE;
        let f = pos.fract();
        self[p00].clone() * (1.0 - f.x) * (1.0 - f.y)
            + self[p10].clone() * f.x * (1.0 - f.y)
            + self[p01].clone() * (1.0 - f.x) * f.y
            + self[p11].clone() * f.x * f.y
    }
    fn distribute(&mut self, pos: Vec2, value: T)
    where
        T: AddAssign<T>,
    {
        let pos = pos - self.frac_offset;
        let p00 = pos.floor().as_ivec2();
        let p10 = p00 + IVec2::X;
        let p01 = p00 + IVec2::Y;
        let p11 = p00 + IVec2::ONE;
        let f = pos.fract();
        self[p00] += value.clone() * (1.0 - f.x) * (1.0 - f.y);
        self[p10] += value.clone() * f.x * (1.0 - f.y);
        self[p01] += value.clone() * (1.0 - f.x) * f.y;
        self[p11] += value.clone() * f.x * f.y;
    }
}

#[derive(Debug, Clone, Copy)]
struct Particle {
    pos: Vec2,
    vel: Vec2,
}

struct Fluid {
    solids: Grid<bool>,
    xvel: Grid<f32>,
    xvel_weights: Grid<f32>,
    yvel: Grid<f32>,
    yvel_weights: Grid<f32>,
    pressure: Grid<f32>,
    next_pressure: Grid<f32>,
    divergence: Grid<f32>,
    mass: Grid<f32>,
}

fn prod(vec: Vec2) -> f32 {
    vec.x * vec.y
}
fn lerp(t: f32, a: f32, b: f32) -> f32 {
    a + (b - a) * t
}

impl Fluid {
    fn advect(&mut self) {
        let last_xvel = self.xvel.clone();
        let last_yvel = self.yvel.clone();
        let last_mass = self.mass.clone();
        self.xvel.set(0.0);
        self.xvel_weights.set(0.0);
        self.yvel.set(0.0);
        self.yvel_weights.set(0.0);
        self.mass.set(0.0);
        last_mass.foreach(|pos, mass| {
            let vel_start_x = last_xvel[pos];
            let vel_start_y = last_yvel[pos];
            let vel_end_x = last_xvel[pos + IVec2::X];
            let vel_end_y = last_yvel[pos + IVec2::Y];
            let a = Vec2::new(vel_start_x, vel_start_y);
            let b = Vec2::new(vel_end_x, vel_end_y) + 1.0;
            let c = b - a;
            let start = a.min(b);
            let end = a.max(b);
            let density = mass / prod(end - start).max(0.0001);
            if density < 0.0001 || (end - start).min_element() < 0.0001 {
                return;
            }
            for i in start.x.floor() as i32..=end.x.floor() as i32 {
                for j in start.y.floor() as i32..=end.y.floor() as i32 {
                    let offset = IVec2::new(i, j);
                    let dst = pos + offset;
                    let offset = offset.as_vec2();
                    if self.solids[dst] {
                        continue;
                    }
                    let intersection = end.min(offset + 1.0) - start.max(offset);
                    let weight = prod(intersection) * density;
                    self.mass[dst] += weight;
                    // can remove for instability if want.
                    let dst_start_inv = ((offset - a) / c).clamp(Vec2::ZERO, Vec2::ONE);
                    let dst_end_inv = ((offset + 1.0 - a) / c).clamp(Vec2::ZERO, Vec2::ONE);
                    self.xvel[dst] += lerp(dst_start_inv.x, vel_start_x, vel_end_x) * weight;
                    // These can be replaced with just dividing by sum  of oposite weights.
                    self.xvel_weights[dst] += weight;
                    self.yvel[dst] += lerp(dst_start_inv.y, vel_start_y, vel_end_y) * weight;
                    self.yvel_weights[dst] += weight;
                    self.xvel[dst + IVec2::X] +=
                        lerp(dst_end_inv.x, vel_start_x, vel_end_x) * weight;
                    self.xvel_weights[dst + IVec2::X] += weight;
                    self.yvel[dst + IVec2::Y] +=
                        lerp(dst_end_inv.y, vel_start_y, vel_end_y) * weight;
                    self.yvel_weights[dst + IVec2::Y] += weight;
                }
            }
        });
        self.xvel = self.xvel.map2(&self.xvel_weights, |pos, x, w| {
            if self.solids[pos] || self.solids[pos - IVec2::X] {
                0.0
            } else {
                x / w.max(0.0001) + gravity.x * dt
            }
        });
        self.yvel = self.yvel.map2(&self.yvel_weights, |pos, x, w| {
            if self.solids[pos] || self.solids[pos - IVec2::Y] {
                0.0
            } else {
                x / w.max(0.0001) + gravity.y * dt
            }
        });
    }
    fn init_pressure(&mut self) {
        self.divergence.load_fn(|pos| {
            let x1 = self.xvel[pos + IVec2::X];
            let x0 = self.xvel[pos];
            let y1 = self.yvel[pos + IVec2::Y];
            let y0 = self.yvel[pos];
            x1 - x0 + y1 - y0
        });
        self.pressure.set(0.0);
    }
    fn pressure_solve(&mut self) {
        for x in (0..self.size().x).rev() {
            for y in (0..self.size().y).rev() {
                let pos = IVec2::new(x, y);
                if self.mass[pos] < 0.0001 {
                    continue;
                }
                if self.solids[pos] {
                    continue;
                }
                let mass = self.mass[pos];
                let ideal_value = (self.divergence[pos] - (mass - 1.0)) * mass;
                let pressure = self.pressure[pos];
                let adj_pressures = [
                    (-1, 0, -self.xvel[pos], self.xvel_weights[pos]),
                    (
                        1,
                        0,
                        self.xvel[pos + IVec2::X],
                        self.xvel_weights[pos + IVec2::X],
                    ),
                    (0, -1, -self.yvel[pos], self.yvel_weights[pos]),
                    (
                        0,
                        1,
                        self.yvel[pos + IVec2::Y],
                        self.yvel_weights[pos + IVec2::Y],
                    ),
                ]
                .into_iter()
                .map(|(dx, dy, vel, weight)| {
                    let pos = pos + IVec2::new(dx, dy);
                    if self.solids[pos] {
                        pressure + vel * weight
                    } else {
                        self.pressure[pos]
                    }
                })
                .sum::<f32>();

                self.next_pressure[pos] = (adj_pressures - ideal_value) / 4.0;
            }
        }
        std::mem::swap(&mut self.pressure, &mut self.next_pressure);
    }
    fn finish_pressure(&mut self) {
        for x in 0..self.size().x {
            for y in 0..self.size().y {
                let pos = IVec2::new(x, y);
                let p00 = self.pressure[pos];
                let p10 = self.pressure[pos - IVec2::X];
                let p01 = self.pressure[pos - IVec2::Y];
                if !self.solids[pos] {
                    if !self.solids[pos - IVec2::X] {
                        self.xvel[pos] -= (p00 - p10) / self.xvel_weights[pos].max(0.00001);
                    }
                    if !self.solids[pos - IVec2::Y] {
                        self.yvel[pos] -= (p00 - p01) / self.yvel_weights[pos].max(0.00001);
                    }
                }
            }
        }
    }
    fn step(&mut self) {
        self.init_pressure();
        for _ in 0..200 {
            self.pressure_solve();
        }
        self.finish_pressure();
        self.advect();
    }
    fn init_grid(width: u32, height: u32) -> Self {
        let size = UVec2::new(width, height).as_ivec2();
        let mut solids = Grid::new(size, true);
        solids.load_fn(|IVec2 { x, y }| x == 0 || y == 0 || x == size.x - 1 || y == size.y - 1);
        Self {
            solids,
            xvel: Grid::with_offset(size + IVec2::new(1, 2), Vec2::new(0.0, -0.5), 0.0),
            xvel_weights: Grid::with_offset(size + IVec2::new(1, 2), Vec2::new(0.0, -0.5), 0.0),
            yvel: Grid::with_offset(size + IVec2::new(2, 1), Vec2::new(-0.5, 0.0), 0.0),
            yvel_weights: Grid::with_offset(size + IVec2::new(2, 1), Vec2::new(-0.5, 0.0), 0.0),
            pressure: Grid::with_offset(size, Vec2::new(0.5, 0.5), 0.0),
            next_pressure: Grid::with_offset(size, Vec2::new(0.5, 0.5), 0.0),
            divergence: Grid::with_offset(size, Vec2::new(0.5, 0.5), 0.0),
            mass: Grid::with_offset(size, Vec2::new(0.5, 0.5), 0.0),
        }
    }
    fn fill_rect(&mut self, start: IVec2, size: IVec2) {
        for y in start.y..start.y + size.y {
            for x in start.x..start.x + size.x {
                let pos = IVec2::new(x, y);
                self.mass[pos] = 1.0;
            }
        }
    }
    fn draw_grid(&self, scale: f32) {
        self.mass.foreach(|pos, density| {
            let color = if self.solids[pos] {
                RED
            } else {
                Color::from_vec((Vec3::splat(1.0) * density / 3.0).extend(1.0))
            };
            let pos = pos.as_vec2() * scale;
            draw_rectangle(pos.x, screen_height() - pos.y - scale, scale, scale, color);
        })
    }
    fn draw_pressure(&self, scale: f32) {
        self.pressure.foreach(|pos, pressure| {
            let color = if self.solids[pos] {
                RED
            } else {
                Color::from_vec(Vec3::splat(pressure.log2() / 20.0).extend(1.0))
            };
            let pos = pos.as_vec2() * scale;
            draw_rectangle(pos.x, screen_height() - pos.y - scale, scale, scale, color);
        })
    }
    fn size(&self) -> IVec2 {
        self.mass.size
    }
}

#[macroquad::main("BasicShapes")]
async fn main() {
    let mut paused = false;
    let mut pressure = false;
    let mut density = true;

    let mut fluid = Fluid::init_grid(200, 100);
    fluid.fill_rect(IVec2::new(5, 5), IVec2::new(100, 70));

    request_new_screen_size(fluid.size().x as f32 * 8.0, fluid.size().y as f32 * 8.0);

    let start = Instant::now();
    let mut i = 0;

    loop {
        clear_background(BLACK);

        if is_key_pressed(KeyCode::Space) || is_key_pressed(KeyCode::Escape) {
            paused = !paused;
        }

        if !paused || is_key_pressed(KeyCode::Period) {
            fluid.step();
        }
        if is_key_pressed(KeyCode::P) {
            pressure = !pressure;
        }
        if is_key_pressed(KeyCode::G) {
            density = !density;
        }

        i += 1;
        if i % 60 == 0 {
            let elapsed = start.elapsed().as_secs_f32();
            println!("FPS: {}", i as f32 / elapsed);
        }

        if density {
            fluid.draw_grid(8.0);
        }
        if pressure {
            fluid.draw_pressure(8.0);
        }

        next_frame().await
    }
}
