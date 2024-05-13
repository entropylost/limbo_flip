use std::{
    f32::consts::TAU,
    ops::{Add, AddAssign, Div, Index, IndexMut, Mul},
    time::Instant,
};

use ::rand::{random, seq::SliceRandom, thread_rng};
use macroquad::prelude::*;
use smallvec::SmallVec;

#[allow(non_upper_case_globals)]
const GRAVITY: Vec2 = Vec2::new(0.0, -30.0);
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

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ParticleType {
    Water,
    Air,
    Oil,
}
impl ParticleType {
    fn density(&self) -> f32 {
        match self {
            ParticleType::Water => 1.0,
            ParticleType::Air => 0.1,
            ParticleType::Oil => 0.8,
        }
    }
    fn color(&self) -> Color {
        match self {
            ParticleType::Water => BLUE,
            ParticleType::Air => Color::from_vec(Vec4::new(1.0, 1.0, 1.0, 0.2)),
            ParticleType::Oil => Color::from_vec(Vec4::new(0.5, 0.5, 0.5, 1.0)),
        }
    }
    fn rest_density(&self) -> f32 {
        match self {
            ParticleType::Water => 4.0,
            ParticleType::Air => 0.0,
            ParticleType::Oil => 4.0 * 0.8,
        }
    }
    fn gravity(&self) -> Vec2 {
        match self {
            ParticleType::Water => GRAVITY,
            ParticleType::Air => Vec2::ZERO,
            ParticleType::Oil => GRAVITY,
        }
    }
}

#[derive(Debug, Clone, Copy)]
struct Particle {
    pos: Vec2,
    vel: Vec2,
    ty: ParticleType,
}

struct Fluid {
    particles: Vec<Particle>,
    solids: Grid<bool>,
    xvel: Grid<f32>,
    xvel_weights: Grid<f32>,
    last_xvel: Grid<f32>,
    yvel: Grid<f32>,
    yvel_weights: Grid<f32>,
    last_yvel: Grid<f32>,
    pressure: Grid<f32>,
    next_pressure: Grid<f32>,
    divergence: Grid<f32>,
    density: Grid<f32>,
    rest_density: Grid<f32>,
    // Contains particles in area [x..x+1) x [y..y+1).
    grid_particles: Grid<SmallVec<[u32; 6]>>,
}

impl Fluid {
    fn advect(&mut self) {
        for p in &mut self.particles {
            p.vel += p.ty.gravity() * dt;
            p.vel += 0.01 * Vec2::from_angle(random::<f32>() * TAU);
            if p.vel.is_nan() {
                panic!("nan velocity");
            }
            p.pos += p.vel * dt;
        }
    }
    fn clamp(&mut self) {
        let size = self.size().as_vec2();
        for p in &mut self.particles {
            let pos = &mut p.pos;
            if pos.x < 1.0 + particle_radius {
                pos.x = 1.0 + particle_radius;
                p.vel.x = 0.0;
            }
            if pos.y < 1.0 + particle_radius {
                pos.y = 1.0 + particle_radius;
                p.vel.y = 0.0;
            }
            if pos.x > size.x - 1.0 - particle_radius {
                pos.x = size.x - 1.0 - particle_radius;
                p.vel.x = 0.0;
            }
            if pos.y > size.y - 1.0 - particle_radius {
                pos.y = size.y - 1.0 - particle_radius;
                p.vel.y = 0.0;
            }
        }
    }
    fn remap(&mut self) {
        self.grid_particles.set(SmallVec::new());
        for (i, p) in self.particles.iter().enumerate() {
            self.grid_particles[p.pos.floor().as_ivec2()].push(i as u32);
        }
    }
    fn p2g(&mut self) {
        self.xvel.set(0.0);
        self.xvel_weights.set(0.0);
        self.yvel.set(0.0);
        self.yvel_weights.set(0.0);
        self.density.set(0.0);
        self.rest_density.set(0.0);
        for p in &self.particles {
            let density = p.ty.density();
            self.xvel.distribute(p.pos, p.vel.x * density);
            self.xvel_weights.distribute(p.pos, density);
            self.yvel.distribute(p.pos, p.vel.y * density);
            self.yvel_weights.distribute(p.pos, density);
            self.density.distribute(p.pos, density);
            self.rest_density
                .distribute(p.pos, p.ty.rest_density() * density);
        }
        self.xvel = self.xvel.map2(&self.xvel_weights, |pos, x, w| {
            if self.solids[pos] || self.solids[pos - IVec2::X] {
                0.0
            } else {
                x / w.max(0.0001)
            }
        });
        self.yvel = self.yvel.map2(&self.yvel_weights, |pos, x, w| {
            if self.solids[pos] || self.solids[pos - IVec2::Y] {
                0.0
            } else {
                x / w.max(0.0001)
            }
        });
        self.rest_density = self
            .rest_density
            .map(|pos, x| x / self.density[pos].max(0.0001));
        self.last_xvel.load_fn(|pos| self.xvel[pos]);
        self.last_yvel.load_fn(|pos| self.yvel[pos]);
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
                if self.grid_particles[pos].is_empty() {
                    continue;
                }
                if self.solids[pos] {
                    continue;
                }
                let density = self.density[pos];
                let rest_density = self.rest_density[pos];
                let ideal_value = (self.divergence[pos] - (density - rest_density)) * density;
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
    fn g2p(&mut self, flip_ratio: f32) {
        for p in &mut self.particles {
            p.vel.x =
                self.xvel.sample(p.pos) + (p.vel.x - self.last_xvel.sample(p.pos)) * flip_ratio;
            p.vel.y =
                self.yvel.sample(p.pos) + (p.vel.y - self.last_yvel.sample(p.pos)) * flip_ratio;
        }
    }
    fn step(&mut self, flip_ratio: f32) {
        self.p2g();
        self.init_pressure();
        for _ in 0..200 {
            self.pressure_solve();
        }
        self.finish_pressure();
        self.g2p(flip_ratio);
        self.advect();
        self.clamp();
        self.remap();
        self.random_collide();
        self.clamp();
        self.remap();
    }
    fn random_collide(&mut self) {
        self.grid_particles.foreach(|_pos, mut particles| {
            let particles = &mut *particles;
            particles.shuffle(&mut thread_rng());
            for ixs in particles.chunks_exact(2) {
                let p1 = self.particles[ixs[0] as usize];
                let p2 = self.particles[ixs[1] as usize];
                let dist = p1.pos.distance(p2.pos);
                if dist < 2.0 * particle_radius {
                    if let Some(normal) = (p1.pos - p2.pos).try_normalize() {
                        // TODO: Adjust for particle type.
                        let mass_portion = p2.ty.density() / (p1.ty.density() + p2.ty.density());
                        let move_dist = 2.0 * particle_radius - dist;
                        self.particles[ixs[0] as usize].pos += normal * move_dist * mass_portion;
                        self.particles[ixs[1] as usize].pos -=
                            normal * move_dist * (1.0 - mass_portion);
                    }
                }
            }
        })
    }
    fn init_grid(width: u32, height: u32) -> Self {
        let size = UVec2::new(width, height).as_ivec2();
        let mut solids = Grid::new(size, true);
        solids.load_fn(|IVec2 { x, y }| x == 0 || y == 0 || x == size.x - 1 || y == size.y - 1);
        Self {
            particles: Vec::new(),
            solids,
            xvel: Grid::with_offset(size + IVec2::new(1, 2), Vec2::new(0.0, -0.5), 0.0),
            xvel_weights: Grid::with_offset(size + IVec2::new(1, 2), Vec2::new(0.0, -0.5), 0.0),
            last_xvel: Grid::with_offset(size + IVec2::new(1, 2), Vec2::new(0.0, -0.5), 0.0),
            yvel: Grid::with_offset(size + IVec2::new(2, 1), Vec2::new(-0.5, 0.0), 0.0),
            yvel_weights: Grid::with_offset(size + IVec2::new(2, 1), Vec2::new(-0.5, 0.0), 0.0),
            last_yvel: Grid::with_offset(size + IVec2::new(2, 1), Vec2::new(-0.5, 0.0), 0.0),
            pressure: Grid::with_offset(size, Vec2::new(0.5, 0.5), 0.0),
            next_pressure: Grid::with_offset(size, Vec2::new(0.5, 0.5), 0.0),
            divergence: Grid::with_offset(size, Vec2::new(0.5, 0.5), 0.0),
            density: Grid::with_offset(size, Vec2::new(0.5, 0.5), 0.0),
            rest_density: Grid::with_offset(size, Vec2::new(0.5, 0.5), 0.0),
            grid_particles: Grid::new(size, SmallVec::new()),
        }
    }
    fn fill_rect(&mut self, start: IVec2, size: IVec2, ty: ParticleType) {
        for y in start.y..start.y + size.y {
            for x in start.x..start.x + size.x {
                let pos = IVec2::new(x, y);
                for i in 0..2 {
                    for j in 0..2 {
                        let particle = Particle {
                            pos: pos.as_vec2()
                                + Vec2::new(i as f32, j as f32) * 0.5
                                + Vec2::new(random::<f32>() * 0.5, random::<f32>() * 0.5),
                            vel: Vec2::ZERO,
                            ty,
                        };
                        self.particles.push(particle);
                    }
                }
            }
        }
    }
    fn draw_grid(&self, scale: f32) {
        self.density.foreach(|pos, particles| {
            let color = if self.solids[pos] {
                RED
            } else {
                Color::from_vec((Vec3::splat(1.0) * (particles) / 6.0).extend(1.0))
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
    fn draw_particles(&self, scale: f32) {
        for p in &self.particles {
            let pos = p.pos * scale;
            draw_circle(
                pos.x,
                screen_height() - pos.y,
                scale * particle_radius,
                p.ty.color(),
            );
        }
    }
    fn size(&self) -> IVec2 {
        self.grid_particles.size
    }
}

#[macroquad::main("BasicShapes")]
async fn main() {
    let mut paused = false;
    let mut pressure = false;
    let mut particles = true;
    let mut density = false;

    let mut fluid = Fluid::init_grid(200, 100);
    fluid.fill_rect(IVec2::new(80, 60), IVec2::new(40, 30), ParticleType::Water);
    fluid.fill_rect(IVec2::new(5, 5), IVec2::new(170, 40), ParticleType::Oil);
    fluid.remap();

    request_new_screen_size(fluid.size().x as f32 * 8.0, fluid.size().y as f32 * 8.0);

    let start = Instant::now();
    let mut i = 0;

    loop {
        clear_background(BLACK);

        if is_key_pressed(KeyCode::Space) || is_key_pressed(KeyCode::Escape) {
            paused = !paused;
        }

        if !paused || is_key_pressed(KeyCode::Period) {
            fluid.step(0.95);
        }
        if is_key_pressed(KeyCode::P) {
            pressure = !pressure;
        }
        if is_key_pressed(KeyCode::O) {
            particles = !particles;
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
        if particles {
            fluid.draw_particles(8.0);
        }

        next_frame().await
    }
}
