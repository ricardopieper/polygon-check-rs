use shapefile;
use shapefile::record::polygon::PolygonRing;
use shapefile::record::Shape;

use glutin_window::GlutinWindow as Window;
use opengl_graphics::{GlGraphics, OpenGL};
use piston::event_loop::{EventSettings, Events};
use piston::input::{RenderArgs, RenderEvent, UpdateArgs, UpdateEvent};
use piston::window::WindowSettings;
use std::collections::HashSet;

use std::iter::Iterator;
use std::time::Instant;
use std::time::Duration;

const WINDOW_WIDTH: u32 = 800;
const WINDOW_HEIGHT: u32 = 800;

fn min<T>(ls: T) -> f64
where
    T: Iterator<Item = f64>,
{
    ls.fold(f64::MAX, |a, b| a.min(b))
}

fn max<T>(ls: T) -> f64
where
    T: Iterator<Item = f64>,
{
    ls.fold(f64::MIN, |a, b| a.max(b))
}

struct Slab<T> {
    y_start: f64,
    y_end: f64,
    items: Vec<T>,
}

fn sqr(x: f64) -> f64 {
    x * x
}

struct Vertex {
    x: f64,
    y: f64,
}

impl Vertex {
    fn size(&self) -> f64 {
        (self.x * self.x + self.y * self.y).sqrt()
    }
    fn versor(&self) -> Vertex {
        Vertex {
            x: self.x / self.size(),
            y: self.y / self.size(),
        }
    }
    fn sum(p: &Vertex, q: &Vertex) -> Vertex {
        Vertex {
            x: p.x + q.x,
            y: p.y + q.y,
        }
    }
    fn subtract(p: &Vertex, q: &Vertex) -> Vertex {
        Vertex {
            x: p.x - q.x,
            y: p.y - q.y,
        }
    }
    fn midpoint(p: &Vertex, q: &Vertex) -> Vertex {
        Vertex {
            x: (p.x + q.x) / 2.0,
            y: (p.y + q.y) / 2.0,
        }
    }
    fn cross_product(p: &Vertex, q: &Vertex) -> f64 {
        (p.x * q.y) - (q.x * p.y)
    }
    fn distance(&self, p2: &Vertex) -> f64 {
        (sqr(self.x - p2.x) + sqr(self.y - p2.y)).sqrt()
    }
    fn equal(&self, p2: &Vertex) -> bool {
        self.x == p2.x && self.y == p2.y
    }
}
type Vertices = Vec<Vertex>;

struct Polygon {
    vertices: Vec<Vertex>,
    convex_hull: Vec<Vertex>,
    line_color: [f32; 4],
    bounding_box: BoundingBox,
    triangles: Vec<Triangle>,
    triangle_slabs: Vec<Slab<usize>>,
}

impl Polygon {
    fn new(vertices: Vec<Vertex>, line_color: [f32; 4]) -> Polygon {
        let hull = Polygon::convex_hull(&vertices);
        Polygon {
            convex_hull: hull,
            line_color: line_color,
            bounding_box: BoundingBox {
                min_x: min(vertices.iter().map(|v| v.x)),
                max_x: max(vertices.iter().map(|v| v.x)),
                min_y: min(vertices.iter().map(|v| v.y)),
                max_y: max(vertices.iter().map(|v| v.y)),
            },
            vertices: vertices,
            triangles: vec![],
            triangle_slabs: vec![],
        }
    }

    fn convex_hull(vertices: &Vec<Vertex>) -> Vec<Vertex> {
        let mut sorted: Vec<&Vertex> = vertices.iter().collect();
        sorted.sort_unstable_by(|a, b| {
            (*a).x
                .partial_cmp(&(*b).x)
                .unwrap_or(std::cmp::Ordering::Equal)
        });
        let mut hull: Vec<Vertex> = vec![];

        //all_x.sort_unstable_by(|a, b| a.partial_cmp(b).unwrap_or(std::cmp::Ordering::Equal));
        let leftmost = &sorted[0];

        let mut current = &sorted[0];
        let mut next = &sorted[1];

        hull.push(Vertex {
            x: leftmost.x,
            y: leftmost.y,
        });

        let mut x = 0;
        loop {
            for vertex in sorted.iter() {
                let v0 = Vertex::subtract(current, next);
                let v1 = Vertex::subtract(current, vertex);
                let cross = Vertex::cross_product(&v0, &v1);
                if cross > 0.0 {
                    next = vertex;
                }
            }

            if next.x == leftmost.x && next.y == leftmost.y {
                break;
            }

            hull.push(Vertex {
                x: next.x,
                y: next.y,
            });
            current = next;
            next = leftmost;

            x = x + 1;
        }

        hull
    }
    fn update_slabs(&mut self, slab_size: f64) {
        let start = self.bounding_box.min_y as usize;
        let end = self.bounding_box.max_y as usize + slab_size as usize;

        for y in (start..=end).step_by(slab_size as usize) {
            let slab_start = y as f64 - slab_size;
            let slab_end = y as f64;

            let mut slab = Slab {
                y_start: slab_start,
                y_end: slab_end,
                items: vec![],
            };

            let mut index = 0;

            let mut slab_triangles = vec![];

            for triangle in self.triangles.iter() {
                let bbox = &triangle.bounding_box;
                //prove that polygon is outside the slab. If proven, then polygon is not in that slab
                let is_outside_slab = (bbox.min_y < slab_start && bbox.max_y < slab_start)
                    || (bbox.min_y > slab_end && bbox.max_y > slab_end);

                if !is_outside_slab {
                    slab_triangles.push((triangle, index));
                }

                index += 1;
            }

            slab_triangles.sort_unstable_by_key(|(triangle, _)| (triangle.perimeter() * 100.0) as i32);
            slab_triangles.reverse();
            for (_tr, index) in slab_triangles {
                slab.items.push(index);
            }

            self.triangle_slabs.push(slab);
        }
    }
}

struct Circle {
    center: Vertex,
    radius: f64,
}

struct BoundingBox {
    min_x: f64,
    min_y: f64,
    max_x: f64,
    max_y: f64,
}

impl BoundingBox {
    fn check_inclusion_bbox(&self, point: &Point) -> bool {
        return point.x >= self.min_x
            && point.x <= self.max_x
            && point.y >= self.min_y
            && point.y <= self.max_y;
    }
}

struct Edge(usize, usize);

fn find_midpoint(vertices: &Vertices) -> Vertex {
    let mut x_sum = 0.0;
    let mut y_sum = 0.0;
    for v in vertices.iter() {
        x_sum += v.x;
        y_sum += v.y;
    }
    Vertex {
        x: x_sum / vertices.len() as f64,
        y: y_sum / vertices.len() as f64,
    }
}

struct Triangle {
    vertices: [Vertex; 3],
    edges: [Edge; 3],
    circumscribed_circle: Circle,
    num: usize,
    bounding_box: BoundingBox,
}

impl Triangle {
    fn perimeter(&self) -> f64 {

        let a = Vertex::subtract(&self.vertices[0], &self.vertices[1]);
        let b = Vertex::subtract(&self.vertices[1], &self.vertices[2]);
        let c = Vertex::subtract(&self.vertices[2], &self.vertices[0]);

        let mut semi = a.size() + b.size() + c.size();
        semi = semi / 2.0;

        return semi * (semi - a.size()) * (semi - b.size()) * (semi - c.size());
    }
}

//https://en.wikipedia.org/wiki/Circumscribed_circle (Circumcenter coordinates, cartesian coordinates)
fn circumscribed_circle(triangle: &[Vertex; 3]) -> Circle {
    let a: &Vertex = &triangle[0];
    let b: Vertex = Vertex::subtract(&triangle[1], a);
    let c: Vertex = Vertex::subtract(&triangle[2], a);
    let d = 2.0 * (Vertex::cross_product(&b, &c));

    let u_x = (1.0 / d) * ((c.y * (sqr(b.x) + sqr(b.y))) - (b.y * (sqr(c.x) + sqr(c.y))));

    let u_y = (1.0 / d) * ((b.x * (sqr(c.x) + sqr(c.y))) - (c.x * (sqr(b.x) + sqr(b.y))));

    let u = Vertex { x: u_x, y: u_y };
    let radius = u.size();
    let circumcenter = Vertex::sum(&u, a);
    Circle {
        center: circumcenter,
        radius: radius,
    }
}

fn build_supertriangle(poly: &Polygon) -> Triangle {
    let mid = find_midpoint(&poly.vertices);

    let x_length = poly.bounding_box.max_x - poly.bounding_box.min_x;
    let y_length = poly.bounding_box.max_y - poly.bounding_box.min_y;

    let max_len = x_length.max(y_length);
    let vertices = [
        Vertex {
            x: mid.x,
            y: mid.y - (2.0 * max_len),
        },
        Vertex {
            x: mid.x - (2.0 * max_len),
            y: mid.y + max_len,
        },
        Vertex {
            x: mid.x + (2.0 * max_len),
            y: mid.y + max_len,
        },
    ];

    Triangle {
        bounding_box: BoundingBox {
            min_x: min(vertices.iter().map(|v| v.x)),
            max_x: max(vertices.iter().map(|v| v.x)),
            min_y: min(vertices.iter().map(|v| v.y)),
            max_y: max(vertices.iter().map(|v| v.y)),
        },
        circumscribed_circle: circumscribed_circle(&vertices),
        vertices: vertices,
        edges: [Edge(0, 1), Edge(1, 2), Edge(2, 0)],
        num: 0,
    }
}

fn is_in_circle(circle: &Circle, point: &Vertex) -> bool {
    let epsilon: f64 = 1e-9;
    let d = circle.center.distance(point);
    return (d < circle.radius + epsilon) || (d < circle.radius - epsilon);
}

fn find_triangles_with_vertex_inside<'a>(
    triangles: &'a Vec<Triangle>,
    vertex: &Vertex,
) -> Vec<&'a Triangle> {
    let mut triangles_found = vec![];
    for t in triangles.iter() {
        let circle = &t.circumscribed_circle;
        if is_in_circle(circle, vertex) {
            triangles_found.push(t)
        }
    }
    triangles_found
}

fn cleanup(poly: &Polygon, mut triangles: Vec<Triangle>) -> Vec<Triangle> {
    //build some lists
    let mut original_edges: Vec<(&Vertex, &Vertex)> = vec![];

    for idx in 0..poly.vertices.len() {
        let mut idx2 = idx + 1;
        if idx == poly.vertices.len() - 1 {
            idx2 = 0
        }
        original_edges.push((&poly.vertices[idx], &poly.vertices[idx2]))
    }

    let mut all_triangle_edges: Vec<(&Vertex, &Vertex, usize)> = vec![];
    for triangle in triangles.iter() {
        for edge in triangle.edges.iter() {
            all_triangle_edges.push((&triangle.vertices[edge.0], &triangle.vertices[edge.1], triangle.num));
        }
    }

    //get only edges that are not in the original edges
    let mut edges_to_check = vec![];
    for (vertex1, vertex2, triangle_num) in all_triangle_edges.iter() {
        
        let mut is_original = false;
        for (original_vertex1, original_vertex2) in original_edges.iter() {

            if (original_vertex1.equal(vertex1) && original_vertex2.equal(vertex2)) || 
                (original_vertex2.equal(vertex1) && original_vertex1.equal(vertex2)) {
                is_original = true;
                break;
            }
        }
        if is_original { continue; }

        edges_to_check.push((*vertex1, *vertex2, *triangle_num));
    }

    let mut numbers_to_delete = HashSet::new();

    //for each triangle edge, find all edges whose midpoint is outside the original shape
    for (vertex1, vertex2, triangle_num) in edges_to_check {
        let midpoint_edge = Vertex::midpoint(vertex1, vertex2);

        let is_inside = App::check_inclusion_concave(poly, &Point {x: midpoint_edge.x, y: midpoint_edge.y, member_of: -1 });

        if is_inside { 
            continue
        }
        
        numbers_to_delete.insert(triangle_num);
    }

    triangles.retain(|x| !numbers_to_delete.contains(&x.num));
    triangles
}

//https://en.wikipedia.org/wiki/Bowyer%E2%80%93Watson_algorithm
fn triangulate(poly: &Polygon) -> Vec<Triangle> {
    let mut triangles: Vec<Triangle> = vec![];

    //build supertriangle
    let supertriangle = build_supertriangle(&poly);
    //copy the supertriangle for later. first one will be consumed by the bower watson algorithm
    let supertriangle2 = build_supertriangle(&poly);

    triangles.push(supertriangle);

    let mut num = 1;

    for vertex in poly.vertices.iter() {
        let bad_triangles = find_triangles_with_vertex_inside(&triangles, vertex);
        let mut polygon: Vec<[Vertex; 2]> = vec![];

        for triangle in bad_triangles.iter() {
            for edge in triangle.edges.iter() {
                let point_a = &triangle.vertices[edge.0];
                let point_b = &triangle.vertices[edge.1];
                let other_bad_triangles = bad_triangles.iter().filter(|x| x.num != triangle.num);
                let mut is_shared = false;
                for other_triangle in other_bad_triangles {
                    for other_edge in other_triangle.edges.iter() {
                        let other_point_a = &other_triangle.vertices[other_edge.0];
                        let other_point_b = &other_triangle.vertices[other_edge.1];

                        if (point_a.equal(other_point_a) && point_b.equal(other_point_b))
                            || (point_b.equal(other_point_a) && point_a.equal(other_point_b))
                        {
                            is_shared = true;
                            break;
                        }
                    }
                    if is_shared {
                        break;
                    }
                }
                if !is_shared {
                    polygon.push([
                        Vertex {
                            x: point_a.x,
                            y: point_a.y,
                        },
                        Vertex {
                            x: point_b.x,
                            y: point_b.y,
                        },
                    ]);
                }
            }
        }

        let mut to_delete = HashSet::new();

        for triangle in bad_triangles {
            to_delete.insert(triangle.num);
        }

        triangles.retain(|x| !to_delete.contains(&x.num));

        for [edge1, edge2] in polygon.into_iter() {
            let triangle_vertices = [
                edge1,
                edge2,
                Vertex {
                    x: vertex.x,
                    y: vertex.y,
                },
            ];

            let triangle = Triangle {
                bounding_box: BoundingBox {
                    min_x: min(triangle_vertices.iter().map(|v| v.x)),
                    max_x: max(triangle_vertices.iter().map(|v| v.x)),
                    min_y: min(triangle_vertices.iter().map(|v| v.y)),
                    max_y: max(triangle_vertices.iter().map(|v| v.y)),
                },
                circumscribed_circle: circumscribed_circle(&triangle_vertices),
                vertices: triangle_vertices,
                edges: [Edge(0, 1), Edge(1, 2), Edge(2, 0)],
                num: num,
            };
            num += 1;

            triangles.push(triangle)
        }
    }

    let mut to_delete = HashSet::new();
    for super_vertex in supertriangle2.vertices.iter() {
        for triangle in triangles.iter() {
            let mut found = false;
            for vertex in triangle.vertices.iter() {
                if super_vertex.equal(&vertex) {
                    found = true;
                    break;
                }
            }
            if found {
                to_delete.insert(triangle.num);
            }
        }
    }

    triangles.retain(|x| !to_delete.contains(&x.num));
   
    return cleanup(poly, triangles);
    //return triangles;
}

#[derive(Debug)]
struct Point {
    x: f64,
    y: f64,
    member_of: i32,
}

fn domain_transform(
    value: f64,
    source_min: f64,
    source_max: f64,
    target_min: f64,
    target_max: f64,
) -> f64 {
    let source_range = source_max - source_min;
    let target_range = target_max - target_min;

    let offset_in_source = value - source_min;

    target_min + ((offset_in_source / source_range) * target_range)
}

fn rescale(
    raw_points: Vec<Vertex>,
    x_range_start: f64,
    x_range_end: f64,
    y_range_start: f64,
    y_range_end: f64,
) -> Vec<Vertex> {
    let mut all_x: Vec<f64> = raw_points.iter().map(|x| x.x).collect();
    all_x.sort_unstable_by(|a, b| a.partial_cmp(b).unwrap_or(std::cmp::Ordering::Equal));

    let mut all_y: Vec<f64> = raw_points.iter().map(|x| x.y).collect();
    all_y.sort_unstable_by(|a, b| a.partial_cmp(b).unwrap_or(std::cmp::Ordering::Equal));

    let min_x = all_x[0];
    let min_y = all_y[0];
    let max_x = *all_x.last().unwrap();
    let max_y = *all_y.last().unwrap();

    raw_points
        .iter()
        .map(|x: &Vertex| Vertex {
            x: domain_transform(x.x, min_x, max_x, x_range_start, x_range_end),
            y: domain_transform(x.y, min_y, max_y, y_range_start, y_range_end),
        })
        .collect()
}

fn has_intersection(k: &Vertex, l: &Vertex, m: &Vertex, n: &Vertex) -> bool {
    //bounding box check
    {
        let minx_kl = k.x.min(l.x);
        let maxx_kl = k.x.max(l.x);

        let minx_mn = m.x.min(n.x);
        let maxx_mn = m.x.max(n.x);

        if (minx_mn < minx_kl && maxx_mn < minx_kl) || (minx_mn > maxx_kl && maxx_mn > maxx_kl) {
            return false;
        }
    }

    {
        let miny_kl = k.y.min(l.y);
        let maxy_kl = k.y.max(l.y);

        let miny_mn = m.y.min(n.y);
        let maxy_mn = m.y.max(n.y);

        if (miny_mn < miny_kl && maxy_mn < miny_kl) || (miny_mn > maxy_kl && maxy_mn > maxy_kl) {
            return false;
        }
    }

    let det = (n.x - m.x) * (l.y - k.y) - (n.y - m.y) * (l.x - k.x);
    if det == 0.0 {
        false
    } else {
        let s = ((n.x - m.x) * (m.y - k.y) - (n.y - m.y) * (m.x - k.x)) / det;
        let t = ((l.x - k.x) * (m.y - k.y) - (l.y - k.y) * (m.x - k.x)) / det;
        s >= 0.0 && s <= 1.0 && t >= 0.0 && t <= 1.0
    }
}

struct App {
    gl: GlGraphics, // OpenGL drawing backend.
    polygon: Vec<Polygon>,
    points: Vec<Point>
}

impl App {
    fn new(gl: GlGraphics, polygons: Vec<Polygon>) -> Self {
        let mut meter = self_meter::Meter::new(Duration::new(0, 0)).unwrap();
        meter.track_current_thread("new");
        meter.scan();

        // let mut rng = rand::thread_rng();
        let start = Instant::now();
        let mut points = vec![];

        let number_of_points = WINDOW_WIDTH * WINDOW_HEIGHT;

        for x in 0..WINDOW_WIDTH {
            for y in 0..WINDOW_HEIGHT {
                points.push(Point {
                    x: x as f64,
                    y: y as f64,
                    member_of: -1,
                });
            }
        }
        let finish = start.elapsed();
        println!("generated points in {:?}", finish);

        let mut polygons = App::build_polygons(polygons);

        let mut slabs = vec![];
        let slab_size = 25.0;

        {
            let start = Instant::now();
            //App::inclusion_in_concave(meter, &polygons, &mut points);
            let finish = start.elapsed();
            println!(
                "Concave: Finished = {:?}, time per operation = {:?}",
                finish, finish.as_nanos().checked_div(number_of_points as u128)
            );
            meter.scan().map_err(|e| println!("Scan error: {}", e)).ok();
            println!("Mem usage: {:#?}", (meter.report().unwrap().memory_rss as f32 / 1000000 as f32));
        }

        for y in (slab_size as u32..=WINDOW_HEIGHT).step_by(slab_size as usize) {
            let slab_start = y as f64 - slab_size;
            let slab_end = y as f64;

            let mut slab = Slab {
                y_start: slab_start,
                y_end: slab_end,
                items: vec![],
            };

            let mut index = 0;
            for polygon in polygons.iter() {
                let bbox = &polygon.bounding_box;
                //prove that polygon is outside the slab. If proven, then polygon is not in that slab
                let is_outside_slab = (bbox.min_y < slab_start && bbox.max_y < slab_start)
                    || (bbox.min_y > slab_end && bbox.max_y > slab_end);

                if !is_outside_slab {
                    slab.items.push(index);
                }

                index += 1;
            }
            slabs.push(slab);
        }

        {
            let start = Instant::now();
            //App::inclusion_in_concave_slabs(&polygons, &slabs, &mut points);
            let finish = start.elapsed();
            println!(
                "Concave + Polygon Slabs: Finished = {:?}, time per operation = {:?}",
                finish, finish.as_nanos().checked_div(number_of_points as u128)
            );
            meter.scan().map_err(|e| println!("Scan error: {}", e)).ok();
            println!("Mem usage: {:#?}", (meter.report().unwrap().memory_rss as f32 / 1000000 as f32));
        }

        {
            let start = Instant::now();
           // App::inclusion_in_convex_hull(&polygons, &mut points);
            let finish = start.elapsed();
            println!(
                "Convex Hull: Finished = {:?}, time per operation = {:?}",
                finish, finish.as_nanos().checked_div(number_of_points as u128)
            );
        }
        {
            let start = Instant::now();
            //App::inclusion_in_bbox(&polygons, &mut points);
            let finish = start.elapsed();
            println!(
                "Bounding Box: Finished = {:?}, time per operation = {:?}",
                finish, finish.as_nanos().checked_div(number_of_points as u128)
            );
            meter.scan().map_err(|e| println!("Scan error: {}", e)).ok();
            println!("Mem usage: {:#?}", (meter.report().unwrap().memory_rss as f32 / 1000000 as f32));
        }

        {
            let start = Instant::now();
            //App::inclusion_in_conv_hull_bbox(&polygons, &mut points);
            let finish = start.elapsed();
            println!(
                "Bounding Box + Convex Hull: Finished = {:?}, time per operation = {:?}",
                finish, finish.as_nanos().checked_div(number_of_points as u128)
            );
            meter.scan()
                .map_err(|e| println!("Scan error: {}", e)).ok();
            println!("Mem usage: {:#?}", (meter.report().unwrap().memory_rss as f32 / 1000000 as f32));
        }

        println!("Triangulating polygons...");

        let start = Instant::now();
        for poly in polygons.iter_mut() {
            poly.triangles = triangulate(poly);
            poly.update_slabs(1.0);
            println!("Triangulated!");
        }
        let finish = start.elapsed();

        println!("Triangulated polygons in Finished = {:?}", finish);

        {
            let start = Instant::now();
            App::inclusion_in_concave_polygon_slabs_and_triangle_slabs(
                &polygons,
                &slabs,
                &mut points,
            );
            let finish = start.elapsed();
            println!(
                "Triangle Slabs: Finished = {:?}, time per operation = {:?}",
                finish, finish.as_nanos().checked_div(number_of_points as u128)
            );
            meter.scan()
                .map_err(|e| println!("Scan error: {}", e)).ok();
            println!("Mem usage: {:#?}", (meter.report().unwrap().memory_rss as f32 / 1000000 as f32));
        }

        {
            let start = Instant::now();
            App::inclusion_in_conv_hull_bbox_triangle_slabs(&polygons, &mut points);
            let finish = start.elapsed();
            println!(
                "Bounding Box + Convex Hull + Triangle Slabs: Finished = {:?}, time per operation = {:?}",
                finish, finish.as_nanos().checked_div(number_of_points as u128)
            );
            meter.scan()
                .map_err(|e| println!("Scan error: {}", e)).ok();
            println!("Mem usage: {:#?}", (meter.report().unwrap().memory_rss as f32 / 1000000 as f32));
        }


        Self {
            gl: gl,
            polygon: polygons,
            points: points,
        }
    }

    fn check_inclusion_concave(polygon: &Polygon, point: &Point) -> bool {
        let start = Vertex { x: 0.0, y: point.y };
        let finish = Vertex {
            x: point.x,
            y: point.y,
        };
        let mut intersections = 0;

        for i in 0 .. polygon.vertices.len() {
            let point1 = &polygon.vertices[i];
            let point2 = if i == polygon.vertices.len() - 1 {
                &polygon.vertices[0]
            } else {
                &polygon.vertices[i + 1]
            };
            
            if has_intersection(point1, point2, &start, &finish) {
                intersections += 1;
            }
        }

        return intersections % 2 != 0;
    }

    fn check_inclusion_triangle_slabs(polygon: &Polygon, point: &Point) -> bool {
        let slab_opt = polygon
            .triangle_slabs
            .iter()
            .find(|s| point.y >= (*s).y_start && point.y <= (*s).y_end);

        if slab_opt.is_none() {
            return false;
        }

        let slab = slab_opt.unwrap();

        //which triangles are part of this slab?

        let triangles_in_slab = slab
            .items
            .iter()
            .map(|index| &polygon.triangles[*index as usize]);

        for triangle in triangles_in_slab {

            let is_in_bbox = triangle.bounding_box.check_inclusion_bbox(point);
            if !is_in_bbox {
                continue;
            }

            let is_in_polygon = App::check_inclusion_convex(&triangle.vertices, point);
            if is_in_polygon {
                return true;
            }
        }
        false
    }

    fn check_inclusion_convex(polygon: &[Vertex], point: &Point) -> bool {
        let mut last_side = -1;
        let target = Vertex {
            x: point.x,
            y: point.y,
        };

        for i in 0..polygon.len() {
            let my_position = &polygon[i];
            let looking_at = if i == polygon.len() - 1 {
                &polygon[0]
            } else {
                &polygon[i + 1]
            };

            let a = Vertex::subtract(looking_at, my_position).versor();
            let b = Vertex::subtract(&target, my_position).versor();

            let cross = Vertex::cross_product(&a, &b);

            let side = if cross > 0.0 { 1 } else { 0 };

            if last_side == -1 {
                last_side = side;
            } else {
                if side != last_side {
                    return false;
                }
                last_side = side;
            }
        }
        return true;
    }

    fn inclusion_in_concave_slabs(
        polygons: &Vec<Polygon>,
        slabs: &Vec<Slab<usize>>,
        points: &mut Vec<Point>,
    ) {
        for point in points {
            point.member_of = -1;

            //which slab does this point belong to?

            let slab_opt = slabs
                .iter()
                .find(|s| point.y >= (*s).y_start && point.y <= (*s).y_end);
            let slab = slab_opt.unwrap();

            //which polygons are part of this slab?

            let polygons_in_slab = slab.items.iter().map(|index| &polygons[*index as usize]);
            let mut poly_index = 0;

            for polygon in polygons_in_slab {
                let is_in_polygon = App::check_inclusion_concave(polygon, &point);
                if is_in_polygon {
                    point.member_of = poly_index;
                }
                poly_index += 1;
            }
        }
    }

    fn inclusion_in_concave_polygon_slabs_and_triangle_slabs(
        polygons: &Vec<Polygon>,
        slabs: &Vec<Slab<usize>>,
        points: &mut Vec<Point>,
    ) {
        for point in points {
            point.member_of = -1;

            //which slab does this point belong to?
            let slab_opt = slabs
                .iter()
                .find(|s| point.y >= (*s).y_start && point.y <= (*s).y_end);
            let slab = slab_opt.unwrap();

            //which polygons are part of this slab?

            let polygons_in_slab = slab.items.iter().map(|index| &polygons[*index as usize]);
            let mut poly_index = 0;

            for polygon in polygons_in_slab {
                let is_in_polygon = App::check_inclusion_triangle_slabs(polygon, &point);
                if is_in_polygon {
                    point.member_of = poly_index;
                    break;
                }
                poly_index += 1;
            }
        }
    }

    fn inclusion_in_concave(polygons: &Vec<Polygon>, points: &mut Vec<Point>) {
        for point in points {
            point.member_of = -1;
            let mut poly_index = 0;
            for polygon in polygons {
                let is_in_polygon = App::check_inclusion_concave(polygon, &point);
                if is_in_polygon {
                    point.member_of = poly_index;
                    break;
                }
                poly_index += 1;
            }
        }
    }

    fn inclusion_in_convex_hull(polygons: &Vec<Polygon>, points: &mut Vec<Point>) {
        for point in points {
            point.member_of = -1;
            let mut poly_index = 0;
            for polygon in polygons {
                if !App::check_inclusion_convex(&polygon.convex_hull, &point) {
                    continue;
                }

                let is_in_polygon = App::check_inclusion_concave(polygon, &point);
                if is_in_polygon {
                    point.member_of = poly_index;
                    break;
                }
                poly_index += 1;
            }
        }
    }

    fn inclusion_in_bbox(polygons: &Vec<Polygon>, points: &mut Vec<Point>) {
        for point in points {
            point.member_of = -1;
            let mut poly_index = 0;
            for polygon in polygons {
                if !polygon.bounding_box.check_inclusion_bbox(&point) {
                    continue;
                }

                let is_in_polygon = App::check_inclusion_concave(polygon, &point);
                if is_in_polygon {
                    point.member_of = poly_index;
                    break;
                }
                poly_index += 1;
            }
        }
    }

    fn inclusion_in_conv_hull_bbox(polygons: &Vec<Polygon>, points: &mut Vec<Point>) {
        for point in points {
            point.member_of = -1;
            let mut poly_index = 0;
            for polygon in polygons {
                if !polygon.bounding_box.check_inclusion_bbox(&point) {
                    continue;
                }

                if !App::check_inclusion_convex(&polygon.convex_hull, &point) {
                    continue;
                }

                let is_in_polygon = App::check_inclusion_concave(polygon, &point);
                if is_in_polygon {
                    point.member_of = poly_index;
                    break;
                }
                poly_index += 1;
            }
        }
    }

    fn inclusion_in_conv_hull_bbox_triangle_slabs(
        polygons: &Vec<Polygon>,
        points: &mut Vec<Point>,
    ) {
        for point in points {
            point.member_of = -1;
            let mut poly_index = 0;
            for polygon in polygons {
                if !polygon.bounding_box.check_inclusion_bbox(&point) {
                    continue;
                }

                if !App::check_inclusion_convex(&polygon.convex_hull, &point) {
                    continue;
                }

                let is_in_polygon = App::check_inclusion_triangle_slabs(polygon, &point);
                if is_in_polygon {
                    point.member_of = poly_index;
                    break;
                }
                poly_index += 1;
            }
        }
    }

    fn build_polygons(polygons: Vec<Polygon>) -> Vec<Polygon> {
        let divider = 3.0;
        let mut i = 0.0;
        let count = polygons.len() as f64;
        let strip_length = count / divider;

        let width = WINDOW_WIDTH as f64 / strip_length;
        let height = WINDOW_HEIGHT as f64 / strip_length;

        //This code lays our the polygons in 3 diagonal strips
        polygons
            .into_iter()
            .map(|polygon| {
                let start_height = ((i % strip_length) * height) / divider //This line lays the polygons in a diagonal in 3 strips
                                    + ((i / strip_length) * (height + height*0.1)); //and this one puts the strips one below the other
                let start_width = (i % strip_length) * width;

                let rescaled = rescale(
                    polygon.vertices,
                    start_width,
                    start_width + width,
                    start_height + height,
                    start_height,
                );

                let new_poly = Polygon::new(rescaled, polygon.line_color);
                i = i + 1.0;

                return new_poly;
            })
            .collect()
    }

    fn render(&mut self, args: &RenderArgs) {
        use graphics::*;

        const BLACK: [f32; 4] = [0.0, 0.0, 0.0, 1.0];

        let polygons = &self.polygon;
        let points = &self.points;

        self.gl.draw(args.viewport(), |c, gl| {
            // Clear the screen.
            clear(BLACK, gl);

            for point in points.iter() {
                let radius = ellipse::circle(point.x, point.y, 1.0);
                let color = if point.member_of == -1 {
                    [1.0, 1.0, 1.0, 1.0]
                } else {
                    [1.0, 0.0, 0.0, 1.0]
                };

                ellipse(color, radius, c.transform, gl);
            }

            for polygon in polygons.iter() {
                let mut last_vertex: Option<&Vertex> = None;
               
                last_vertex = None;
                /*for vertex in polygon.convex_hull.iter() {
                    if let Some(last_vtx) = last_vertex {
                        line(
                            [0.0, 0.0, 0.0, 1.0],
                            1.0,
                            [last_vtx.x, last_vtx.y, vertex.x, vertex.y],
                            c.transform,
                            gl,
                        );
                    }

                    last_vertex = Some(vertex);
                }*/
                
                for triangle in polygon.triangles.iter() {
                    for Edge(e1, e2) in triangle.edges.iter() {
                        let p1 = &triangle.vertices[*e1];
                        let p2 = &triangle.vertices[*e2];
                        line(
                            [0.0, 0.0, 0.0, 1.0],
                            1.0,
                            [p1.x, p1.y, p2.x, p2.y],
                            c.transform,
                            gl,
                        )
                    }
                }
/*
                for vertex in polygon.vertices.iter() {
                    if let Some(last_vtx) = last_vertex {
                        line(
                            polygon.line_color,
                            1.0,
                            [last_vtx.x, last_vtx.y, vertex.x, vertex.y],
                            c.transform,
                            gl,
                        );
                    }

                    last_vertex = Some(vertex);
                    let radius = ellipse::circle(vertex.x, vertex.y, 4.0);
                    ellipse([0.0, 1.0, 0.0, 1.0], radius, c.transform, gl);
                }*/

            }
            
        });
    }

    fn update(&mut self, _args: &UpdateArgs) {
        // Rotate 2 radians per second.
    }
}

fn get_polygon() -> Vec<Vertex> {
    let mut polygons = vec![];
    let reader =
        shapefile::Reader::from_path("./data/dados_geo/estado_rs.shp").unwrap();
    for shape in reader {
        let shape = shape.unwrap();

        if let Shape::Polygon(ref polygon) = shape {
            for ring in polygon.rings() {
                let points = match ring {
                    PolygonRing::Outer(ref points) => points,
                    PolygonRing::Inner(points) => points,
                };

                for point in points {
                    polygons.push(Vertex {
                        x: point.x,
                        y: point.y,
                    })
                }
            }
        } else {
            println!("Shapetype is {}", shape.shapetype());
            println!("{}", shape);
        }
    }
    polygons
}

fn main() {
    // Change this to OpenGL::V2_1 if not working.
    let opengl = OpenGL::V3_2;

    // Create an Glutin window.
    let mut window: Window = WindowSettings::new("RS MAP", [WINDOW_WIDTH, WINDOW_HEIGHT])
        .graphics_api(opengl)
        .exit_on_esc(true)
        .samples(4)
        .build()
        .unwrap();

    // Create a new game and run it.
    let mut app = App::new(
        GlGraphics::new(opengl),
        vec![
            Polygon::new(get_polygon(), [0.0, 0.0, 1.0, 1.0]),
            Polygon::new(get_polygon(), [0.0, 1.0, 0.0, 1.0]),
            Polygon::new(get_polygon(), [0.0, 0.0, 1.0, 1.0]),
            Polygon::new(get_polygon(), [0.0, 1.0, 1.0, 1.0]),
            Polygon::new(get_polygon(), [1.0, 0.0, 1.0, 1.0]),
            Polygon::new(get_polygon(), [1.0, 1.0, 0.0, 1.0]),
            Polygon::new(get_polygon(), [1.0, 1.0, 1.0, 1.0]),
            Polygon::new(get_polygon(), [0.0, 1.0, 0.0, 1.0]),
            Polygon::new(get_polygon(), [0.0, 0.0, 1.0, 1.0]),
            Polygon::new(get_polygon(), [0.0, 1.0, 1.0, 1.0]),
            Polygon::new(get_polygon(), [1.0, 0.0, 1.0, 1.0]),
            Polygon::new(get_polygon(), [1.0, 1.0, 0.0, 1.0]),
            Polygon::new(get_polygon(), [1.0, 1.0, 1.0, 1.0]),
            Polygon::new(get_polygon(), [0.0, 1.0, 0.0, 1.0]),
            Polygon::new(get_polygon(), [0.0, 0.0, 1.0, 1.0]),
            Polygon::new(get_polygon(), [0.0, 1.0, 1.0, 1.0]),
            Polygon::new(get_polygon(), [1.0, 0.0, 1.0, 1.0]),
            Polygon::new(get_polygon(), [1.0, 1.0, 0.0, 1.0])
        ],
    );

    let mut events = Events::new(EventSettings::new());
    while let Some(e) = events.next(&mut window) {
        if let Some(args) = e.render_args() {
            app.render(&args);
        }

        if let Some(args) = e.update_args() {
            app.update(&args);
        }
    }
}
