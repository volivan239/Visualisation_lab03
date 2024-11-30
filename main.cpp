#include <bits/stdc++.h>

using namespace std;

const float INF = 1e9 + 7, EPS = 1e-6;

struct point {
    float x, y;
    point() {}
    point(float x, float y): x(x), y(y) {}
    point operator + (const point &other) const {
        return point(x + other.x, y + other.y);
    }
    point operator - (const point &other) const {
        return point(x - other.x, y - other.y);
    }
    float len2() const {
        return x * x + y * y;
    }
    float len() const {
        return sqrt(len2());
    }
    point mul(float k) const {
        return point(x * k, y * k);
    }
    point norma() const {
        return point(-y, x);
    }
    point normalize() const {
        float l = len();
        return mul(1. / l);
    }
    float operator ^ (const point &other) const {
        return x * other.y - y * other.x;
    }
};

vector <point> main_points;
vector <point> other_points;
float sweep_x;

struct arc {
    mutable int focus_id, next_id;
    mutable int valid_deletion_id = -1;
    arc() {}
    arc(int focus_id, int next_id): focus_id(focus_id), next_id(next_id) {};

    float get_intersection_y(float x) const {
        if (next_id == -1) {
            return INF;
        }
        x += EPS;
        point focus = main_points[focus_id];
        point next = main_points[next_id];
        
        point m = (focus + next).mul(0.5);
        point v = (focus - m).norma();
        float D = (x - focus.x) * (x - next.x);
        return m.y + ((m.x - x) * v.x + sqrt(D) * v.len()) / v.y;
    }

    bool operator < (const arc &other) const {
        return get_intersection_y(sweep_x) < other.get_intersection_y(sweep_x);
    }
    
    bool operator < (const float &y) const {
        return get_intersection_y(sweep_x) < y;
    }
};

struct event {
    char event_type;
    int event_id;
    int point_id;
    set<arc, less<>>::iterator pt;
    float x;
    event() {}
    event(char event_type, int event_id, int point_id, set<arc, less<>>::iterator pt, float x): event_type(event_type), event_id(event_id), point_id(point_id), pt(pt), x(x) {}
    bool operator < (const event &other) const {
        return x > other.x;
    }
};

point intersec_lines(point p1, point v1, point p2, point v2) {
    float t = ((p2 ^ v2) - (p1 ^ v2)) / (v1 ^ v2);
    return p1 + v1.mul(t);
}

point circumcenter(point a, point b, point c) {
    return intersec_lines((a + b).mul(0.5), (b - a).norma(), (a + c).mul(0.5), (c - a).norma());
}

float get_y_on_segm(point a, point b, float x) {
    assert(a.x <= x && x <= b.x);
    return a.y + (b.y - a.y) * (x - a.x) / (b.x - a.x);
}

struct triangle {
    int num, a_id, b_id, c_id;
    triangle() {}
    triangle(int num, int a_id, int b_id, int c_id): num(num) {
        vector <int> v = {a_id, b_id, c_id};
        sort(v.begin(), v.end(), [&](int a, int b) { return main_points[a].x < main_points[b].x; });
        this->a_id = v[0];
        this->b_id = v[1];
        this->c_id = v[2];
    }

    pair<float, float> get_projection(float x) const {
        assert(main_points[a_id].x <= x && x <= main_points[c_id].x);
        float longer_y = get_y_on_segm(main_points[a_id], main_points[c_id], x);
        float shorter_y;
        if (x < main_points[b_id].x) {
            shorter_y = get_y_on_segm(main_points[a_id], main_points[b_id], x);
        } else {
            shorter_y = get_y_on_segm(main_points[b_id], main_points[c_id], x);
        }
        return {min(shorter_y, longer_y), max(shorter_y, longer_y)};
    }

    bool operator < (const triangle &other) const {
        float y1 = get_projection(sweep_x).second;
        float y2 = other.get_projection(sweep_x).second;
        if (y1 != y2) {
            assert(num != other.num);
            return y1 < y2;
        }
        return num < other.num;
    }
    bool operator < (const float &y) const {
        return get_projection(sweep_x).second < y;
    }
};

struct Fortune {
    set<arc, less<>> arcs;
    int last_event_id = 0;
    priority_queue<event> events;
    vector<triangle> result;

    Fortune() {}

    void recalc_delete_events(set<arc, less<>>::iterator it) {
        if (it == arcs.begin() || it->next_id == -1) {
            return;
        }

        auto prv = it;
        prv--;
        point a = main_points[prv->focus_id];
        assert(prv->next_id == it->focus_id);
        point b = main_points[it->focus_id];
        point c = main_points[it->next_id];
        point cc = circumcenter(a, b, c);
        float xx = cc.x + (cc - a).len();
        if (xx < sweep_x - EPS || prv->get_intersection_y(xx) + EPS < it->get_intersection_y(xx)) {
            return;
        }
        it->valid_deletion_id = last_event_id;
        events.push(event('-', last_event_id++, it->focus_id, it, xx));
    }

    void insert(int id) {
        if (arcs.empty()) {
            arcs.insert(arc(id, -1));
            return;
        }

        auto nxt = arcs.lower_bound(main_points[id].y);
        arcs.insert(arc(id, nxt->focus_id));
        arcs.insert(arc(nxt->focus_id, id));
        recalc_delete_events(nxt);
        --nxt;
        recalc_delete_events(--nxt);
    }

    void erase(set<arc, less<>>::iterator it) {
        auto prv = it, nxt = it;
        assert(it != arcs.begin());
        --prv;
        ++nxt;
        assert(nxt != arcs.end());

        int a_id = it->focus_id;
        int b_id = prv->focus_id;
        int c_id = nxt->focus_id;
        result.emplace_back(result.size(), a_id, b_id, c_id);

        arcs.erase(it);
        prv->next_id = c_id;
        recalc_delete_events(prv);
        recalc_delete_events(nxt);
    }
    
    vector<triangle> solve() {
        int n = main_points.size();
        for (int i = 0; i < n; i++) {
            events.push(event('+', last_event_id++, i, arcs.end(), main_points[i].x));
        }

        while (!events.empty()) {
            auto event = events.top();
            sweep_x = event.x + EPS;
            events.pop();
            if (event.event_type == '-') {
                if (event.event_id != event.pt->valid_deletion_id) {
                    continue;
                }
                erase(event.pt);
            }
            if (event.event_type == '+') {
                insert(event.point_id);
            }
        }
        return result;
    }
};

struct triangle_event {
    char event_type;
    int entity_id;
    float x;
    triangle_event() {}
    triangle_event(char event_type, int entity_id, float x): event_type(event_type), entity_id(entity_id), x(x) {}
    bool operator < (const triangle_event &other) const {
        if (x != other.x) {
            return x < other.x;
        }
        return event_type > other.event_type;
    }
};

struct localizer {
    set<triangle, less<>> triangles_on_sweep;
    vector<triangle> triangles;

    localizer(vector<triangle> triangles): triangles(triangles) {}

    vector<int> solve() {
        vector<triangle_event> events;
        vector<int> ans(other_points.size(), -1);
        for (int i = 0; i < (int) triangles.size(); i++) {
            events.emplace_back('+', i, main_points[triangles[i].a_id].x);
            events.emplace_back('-', i, main_points[triangles[i].c_id].x);
        }
        for (int i = 0; i < (int) other_points.size(); i++) {
            events.emplace_back('?', i, other_points[i].x);
        }

        sort(events.begin(), events.end());

        for (auto &event : events) {
            sweep_x = event.x;
            if (event.event_type == '+') {
                sweep_x += EPS;
                triangles_on_sweep.insert(triangles[event.entity_id]);
            } else if (event.event_type == '-') {
                sweep_x -= EPS;
                assert(triangles_on_sweep.erase(triangles[event.entity_id]));
            } else {
                float y = other_points[event.entity_id].y;
                auto ptr = triangles_on_sweep.lower_bound(y);
                if (ptr == triangles_on_sweep.end() || (ptr == triangles_on_sweep.begin() && ptr->get_projection(sweep_x).first > y)) {
                    ans[event.entity_id] = -1;
                    continue;
                }
                ans[event.entity_id] = ptr->num;
            }
        }

        return ans;
    }
};

int main() {
    int n, m;
    cin >> n >> m;
    main_points.resize(n);
    other_points.resize(m);
    for (int i = 0; i < n; i++) {
        cin >> main_points[i].x >> main_points[i].y;
    }
    for (int i = 0; i < m; i++) {
        cin >> other_points[i].x >> other_points[i].y;
    }

    auto triangles = Fortune().solve();
    auto triangle_nums = localizer(triangles).solve();

    cout << triangles.size() << endl;
    for (auto [_, a, b, c] : triangles) {
        cout << a << ' ' << b << ' ' << c << '\n';
    }
    for (int i = 0; i < (int) other_points.size(); i++) {
        if (i != 0) {
            cout << ' ';
        }
        cout << triangle_nums[i];
    }
    cout << '\n';
    return 0;
}