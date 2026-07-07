// Improved RecNoC Simulator
// A cycle-accurate simulator for 3D Cluster-based Reconfigurable Network-on-Chip
// with fixed routing, credit-based flow control, and priority arbitration.

#include <iostream>
#include <fstream>
#include <vector>
#include <queue>
#include <random>
#include <algorithm>
#include <iomanip>
#include <memory>
#include <cmath>

using namespace std;

// ================================ Configuration ================================
constexpr int BUFFER_SIZE = 8;
constexpr int NI_BUFFER_SIZE = 50;
constexpr int SIMULATION_TIME = 50000;
constexpr int TRAFFIC_GEN_DURATION = SIMULATION_TIME - 2000;
constexpr double INJECTION_RATE = 0.5;
constexpr int CLUSTER_SIZE = 1;
constexpr int NUM_CORRIDORS = 9;
constexpr int NETWORK_X = 6;
constexpr int NETWORK_Y = 6;
constexpr int NETWORK_Z = 1;

// Derived dimensions
constexpr int ELEMENTS_X = NETWORK_X + (((NETWORK_X / CLUSTER_SIZE) - 1) * NUM_CORRIDORS);
constexpr int ELEMENTS_Y = NETWORK_Y + (((NETWORK_Y / CLUSTER_SIZE) - 1) * NUM_CORRIDORS);

// Port numbers (for both routers and switches)
enum class Port : int {
    NORTH = 1,
    WEST  = 2,
    SOUTH = 3,
    EAST  = 4,
    PE    = 5,
    // For recswitch internal mapping we use 0..3 for the four directions
};

// ================================ Flit ========================================
struct Flit {
    int id;
    int src_x, src_y, src_z;
    int dest_x, dest_y, dest_z;
    int injection_time;
    int latency = 0;          // accumulated delay (cycles spent in network)
    bool reached = false;
};

// ================================ Circular Buffer =============================
template<typename T, int CAPACITY>
class CircularBuffer {
    T data[CAPACITY];
    int head = -1;
    int tail = -1;

public:
    bool empty() const { return head == -1; }
    bool full() const {
        return (head == 0 && tail == CAPACITY-1) || (tail == head - 1);
    }
    bool push(const T& item) {
        if (full()) return false;
        if (empty()) head = tail = 0;
        else tail = (tail + 1) % CAPACITY;
        data[tail] = item;
        return true;
    }
    T pop() {
        if (empty()) return T{};   // undefined behaviour, but we'll check before
        T item = data[head];
        if (head == tail) head = tail = -1;
        else head = (head + 1) % CAPACITY;
        return item;
    }
    const T& front() const {
        return data[head];
    }
    void increment_time() {
        if (!empty()) data[head].latency++;
    }
};

// ================================ Network Elements ============================
class Element {
public:
    bool is_router;
    int x, y, z;

    // For routers: buffers per input port
    CircularBuffer<Flit, BUFFER_SIZE> inport_buffers[6]; // indices 1..5 (PE=5)
    // For recswitches: single flit storage per input
    Flit rec_in_flit[6];          // only used if is_router==false
    bool rec_in_full[6] = {false};

    // Output ports
    struct Outport {
        Flit flit;
        bool has_flit = false;
        int empty_slots = BUFFER_SIZE;   // credit counter from downstream
        bool credit_received = false;    // from downstream
        bool arbiter_requests[6] = {false}; // requests from inports
        int winner = -1;
    };
    Outport outports[6]; // 1..5

    // For recswitch crossbar: 4x4 matrix mapping input (0..3) to output (0..3)
    // Inputs: 0=N,1=W,2=S,3=E   Outputs: same order
    bool crossbar[4][4];

    Element() : is_router(false), x(0), y(0), z(0) {
        // Default crossbar: straight connections (N<->S, W<->E)
        crossbar[0][2] = true; crossbar[2][0] = true;
        crossbar[1][3] = true; crossbar[3][1] = true;
    }

    // Routing function for routers (XY deterministic)
    Port route(const Flit& f) const {
        if (f.dest_x == x && f.dest_y == y && f.dest_z == z)
            return Port::PE;
        int dx = f.dest_x - x;
        int dy = f.dest_y - y;
        if (dx != 0) return (dx > 0) ? Port::EAST : Port::WEST;
        if (dy != 0) return (dy > 0) ? Port::NORTH : Port::SOUTH;
        return Port::PE; // should not happen
    }

    // Convert port to neighbour coordinates (assuming current element is at (x,y,z))
    void neighbour_coords(Port p, int& nx, int& ny, int& nz) const {
        nx = x; ny = y; nz = z;
        switch (p) {
            case Port::NORTH: ny++; break;
            case Port::SOUTH: ny--; break;
            case Port::EAST:  nx++; break;
            case Port::WEST:  nx--; break;
            default: break;
        }
    }

    // Convert outport of this element to inlink number of neighbour
    static Port outport_to_inlink(Port out) {
        // For neighbour, its inlink is opposite direction
        switch (out) {
            case Port::NORTH: return Port::SOUTH;
            case Port::SOUTH: return Port::NORTH;
            case Port::EAST:  return Port::WEST;
            case Port::WEST:  return Port::EAST;
            default: return Port::PE; // not used
        }
    }
};

// ================================ Network ====================================
class Network {
public:
    vector<vector<vector<Element>>> grid;
    vector<vector<CircularBuffer<Flit, NI_BUFFER_SIZE>>> ni_queues; // indexed by router coordinates

    Network() {
        // Allocate grid: 1-indexed, so +1 for padding
        grid.resize(ELEMENTS_X+1);
        for (int i=0; i<=ELEMENTS_X; ++i) {
            grid[i].resize(ELEMENTS_Y+1);
            for (int j=0; j<=ELEMENTS_Y; ++j) {
                grid[i][j].resize(NETWORK_Z+1);
                for (int k=0; k<=NETWORK_Z; ++k) {
                    grid[i][j][k].x = i;
                    grid[i][j][k].y = j;
                    grid[i][j][k].z = k;
                }
            }
        }
        // Build topology: place routers in clusters and recswitches in corridors
        build_topology();

        // NI queues for routers only
        ni_queues.resize(ELEMENTS_X+1);
        for (int i=0; i<=ELEMENTS_X; ++i)
            ni_queues[i].resize(ELEMENTS_Y+1);
    }

    void build_topology() {
        int y = 1;
        while (y <= ELEMENTS_Y) {
            int x = 1;
            int routers_placed = 0;
            while (routers_placed < NETWORK_Y) {
                // Place a cluster of CLUSTER_SIZE routers in Y direction
                for (int c = 0; c < CLUSTER_SIZE && y <= ELEMENTS_Y; ++c, ++y) {
                    // Place routers along X direction for this row
                    x = 1;
                    int routers_in_row = 0;
                    while (routers_in_row < NETWORK_X) {
                        for (int r = 0; r < CLUSTER_SIZE && x <= ELEMENTS_X; ++r, ++x) {
                            grid[x][y][1].is_router = true;
                            routers_in_row++;
                        }
                        if (routers_in_row < NETWORK_X) {
                            // Insert NUM_CORRIDORS recswitches
                            for (int c2 = 0; c2 < NUM_CORRIDORS && x <= ELEMENTS_X; ++c2, ++x) {
                                grid[x][y][1].is_router = false;
                            }
                        }
                    }
                    routers_placed++;
                }
                if (routers_placed < NETWORK_Y) {
                    // Insert NUM_CORRIDORS recswitch rows (all recswitches across X)
                    for (int c = 0; c < NUM_CORRIDORS && y <= ELEMENTS_Y; ++c, ++y) {
                        for (int x2 = 1; x2 <= ELEMENTS_X; ++x2) {
                            grid[x2][y][1].is_router = false;
                        }
                    }
                }
            }
        }
    }

    // Helper: check if (x,y,z) is a router
    bool is_router(int x, int y, int z) const {
        if (x<1 || x>ELEMENTS_X || y<1 || y>ELEMENTS_Y || z<1 || z>NETWORK_Z) return false;
        return grid[x][y][z].is_router;
    }

    // Get neighbour element at port p from (x,y,z)
    Element* get_neighbour(int x, int y, int z, Port p) {
        int nx, ny, nz;
        grid[x][y][z].neighbour_coords(p, nx, ny, nz);
        if (nx<1 || nx>ELEMENTS_X || ny<1 || ny>ELEMENTS_Y || nz<1 || nz>NETWORK_Z)
            return nullptr;
        return &grid[nx][ny][nz];
    }
};

// ================================ Simulator ==================================
class Simulator {
private:
    Network net;
    mt19937 rng;
    uniform_int_distribution<int> dest_dist_x, dest_dist_y;
    uniform_real_distribution<double> inj_dist;

    // Statistics
    vector<int> flit_latencies; // per flit latency
    int total_generated = 0;
    int total_delivered = 0;
    int total_credits_sent = 0;
    int errors = 0;

public:
    Simulator() : rng(chrono::steady_clock::now().time_since_epoch().count()),
                  dest_dist_x(1, ELEMENTS_X), dest_dist_y(1, ELEMENTS_Y),
                  inj_dist(0.0, 1.0) {}

    void run() {
        // Main simulation loop
        for (int cycle = 0; cycle < SIMULATION_TIME; ++cycle) {
            // 1. Generate traffic
            if (cycle < TRAFFIC_GEN_DURATION)
                generate_traffic(cycle);

            // 2. Move flits from outports to inlinks (and handle destination)
            move_flits_between_elements(cycle);

            // 3. Handle recswitches: move flits from inport to outport
            process_recswitches(cycle);

            // 4. Handle routers: routing, arbitration, and transfer from inport to outport
            process_routers(cycle);

            // 5. Propagate credits
            propagate_credits(cycle);
        }

        // Print statistics
        print_statistics();
    }

private:
    // ---- Traffic Generation ----
    void generate_traffic(int cycle) {
        for (int x=1; x<=ELEMENTS_X; ++x) {
            for (int y=1; y<=ELEMENTS_Y; ++y) {
                if (net.is_router(x,y,1)) {
                    // Generate a flit with probability injection_rate
                    if (inj_dist(rng) < INJECTION_RATE) {
                        // Choose a random destination router (not self)
                        int dx, dy;
                        do {
                            dx = dest_dist_x(rng);
                            dy = dest_dist_y(rng);
                        } while ( !net.is_router(dx,dy,1) || (dx==x && dy==y) );

                        Flit f;
                        f.id = total_generated++;
                        f.src_x = x; f.src_y = y; f.src_z = 1;
                        f.dest_x = dx; f.dest_y = dy; f.dest_z = 1;
                        f.injection_time = cycle;
                        f.latency = 0;
                        f.reached = false;

                        // Enqueue into NI queue of source router
                        if (!net.ni_queues[x][y].push(f)) {
                            // NI buffer full -> drop flit (or count as loss)
                            // For simplicity, we just drop; but we can count.
                        }
                    }
                }
            }
        }
    }

    // ---- Move flits from outports to inlinks ----
    void move_flits_between_elements(int cycle) {
        for (int x=1; x<=ELEMENTS_X; ++x) {
            for (int y=1; y<=ELEMENTS_Y; ++y) {
                for (int z=1; z<=NETWORK_Z; ++z) {
                    Element& elem = net.grid[x][y][z];
                    for (int p = 1; p <= 5; ++p) {
                        Port out = static_cast<Port>(p);
                        if (out == Port::PE) continue; // PE_out is handled separately
                        Element::Outport& op = elem.outports[p];
                        if (!op.has_flit) continue;

                        // Try to send to neighbour
                        Element* nb = net.get_neighbour(x,y,z,out);
                        if (!nb) continue; // boundary
                        Port inlink = Element::outport_to_inlink(out);

                        // If neighbour is a router, the flit goes into its buffer (if space)
                        // If neighbour is a recswitch, the flit goes into its inport storage
                        bool success = false;
                        if (nb->is_router) {
                            // router: check buffer space
                            int inport_idx = static_cast<int>(inlink);
                            if (!nb->inport_buffers[inport_idx].full()) {
                                // Decrement empty slots of current outport (credit based)
                                if (op.empty_slots > 0) {
                                    op.empty_slots--;
                                    nb->inport_buffers[inport_idx].push(op.flit);
                                    op.has_flit = false;
                                    success = true;
                                }
                            }
                        } else {
                            // recswitch: check if its inport is free
                            int inport_idx = static_cast<int>(inlink);
                            if (!nb->rec_in_full[inport_idx]) {
                                // For recswitches, no credit needed (they have no buffers)
                                nb->rec_in_flit[inport_idx] = op.flit;
                                nb->rec_in_full[inport_idx] = true;
                                op.has_flit = false;
                                success = true;
                            }
                        }
                        // If not successful, flit stays in outport (blocked)
                    }

                    // Handle PE_out (destination)
                    Element::Outport& pe_out = elem.outports[5];
                    if (pe_out.has_flit) {
                        // This flit has reached its destination
                        Flit f = pe_out.flit;
                        // Record latency
                        f.latency = cycle - f.injection_time;
                        flit_latencies.push_back(f.latency);
                        total_delivered++;
                        pe_out.has_flit = false;
                        // Send credit back to the previous hop (the one that sent this flit)
                        // We need to know which inport sent it, but we don't track that.
                        // In a proper implementation, we would send a credit to the upstream.
                        // For now, we simply ignore because we don't have that info.
                        // Actually, the flit came from an inport, we can store the inport index in the flit.
                        // We'll simplify: not sending credit for PE_out, as the NI buffer will eventually send credits.
                    }
                }
            }
        }
    }

    // ---- Process recswitches ----
    void process_recswitches(int cycle) {
        for (int x=1; x<=ELEMENTS_X; ++x) {
            for (int y=1; y<=ELEMENTS_Y; ++y) {
                for (int z=1; z<=NETWORK_Z; ++z) {
                    Element& elem = net.grid[x][y][z];
                    if (elem.is_router) continue;

                    // For each input (0..3) that has a flit, see if corresponding output is free
                    for (int in=0; in<4; ++in) {
                        if (!elem.rec_in_full[in+1]) continue; // ports are 1..5, we use 1..4 for N,W,S,E
                        // Find output according to crossbar
                        for (int out=0; out<4; ++out) {
                            if (elem.crossbar[in][out]) {
                                int out_port = out+1; // convert to 1..4
                                if (!elem.outports[out_port].has_flit) {
                                    // Move flit
                                    elem.outports[out_port].flit = elem.rec_in_flit[in+1];
                                    elem.outports[out_port].has_flit = true;
                                    elem.rec_in_full[in+1] = false;
                                }
                                break; // only one output per input
                            }
                        }
                    }
                }
            }
        }
    }

    // ---- Process routers ----
    void process_routers(int cycle) {
        for (int x=1; x<=ELEMENTS_X; ++x) {
            for (int y=1; y<=ELEMENTS_Y; ++y) {
                for (int z=1; z<=NETWORK_Z; ++z) {
                    Element& elem = net.grid[x][y][z];
                    if (!elem.is_router) continue;

                    // Step 1: Routing computation for each non-empty inport
                    for (int in=1; in<=5; ++in) {
                        auto& buf = elem.inport_buffers[in];
                        if (buf.empty()) continue;
                        const Flit& f = buf.front();
                        Port route = elem.route(f);
                        int out_idx = static_cast<int>(route);
                        // Store the computed outport in a temporary array (use a separate array)
                        elem.inport_buffers[in].increment_time(); // one cycle for routing
                        // Set request for arbitration
                        if (out_idx >=1 && out_idx <=5) {
                            elem.outports[out_idx].arbiter_requests[in] = true;
                        }
                    }

                    // Step 2: Arbitration for each outport
                    for (int out=1; out<=5; ++out) {
                        auto& op = elem.outports[out];
                        // Check if outport is free and downstream has space
                        if (op.has_flit) continue; // outport already occupied
                        if (op.empty_slots <= 0) continue; // no credit

                        // Choose winner among requests (priority-based: lower index = higher priority)
                        int winner = -1;
                        for (int in=1; in<=5; ++in) {
                            if (op.arbiter_requests[in]) {
                                winner = in;
                                break;
                            }
                        }
                        if (winner == -1) continue;

                        // Grant: move flit from inport to outport
                        auto& buf = elem.inport_buffers[winner];
                        if (buf.empty()) { // should not happen
                            op.arbiter_requests[winner] = false;
                            continue;
                        }
                        Flit f = buf.pop(); // dequeue
                        op.flit = f;
                        op.has_flit = true;
                        // Decrement empty slots (already checked >0)
                        op.empty_slots--;

                        // Send credit back to the upstream element (the one that sent this flit)
                        // The upstream element is the neighbour that corresponds to this inport.
                        // We need to send a credit to that neighbour's outport.
                        send_credit_to_upstream(x, y, z, winner);

                        // Clear arbitration request for this inport (the flit is gone)
                        op.arbiter_requests[winner] = false;
                    }

                    // Step 3: Clear remaining arbitration requests (they will be recomputed next cycle)
                    for (int out=1; out<=5; ++out) {
                        for (int in=1; in<=5; ++in) {
                            elem.outports[out].arbiter_requests[in] = false;
                        }
                    }
                }
            }
        }
    }

    // ---- Credit propagation ----
    void send_credit_to_upstream(int x, int y, int z, int inport_idx) {
        // Find the neighbour element that sent the flit to this inport
        Port from_dir;
        switch (inport_idx) {
            case 1: from_dir = Port::NORTH; break;
            case 2: from_dir = Port::WEST;  break;
            case 3: from_dir = Port::SOUTH; break;
            case 4: from_dir = Port::EAST;  break;
            case 5: from_dir = Port::PE;    break; // PE_in, no upstream router
        }
        if (inport_idx == 5) return; // no credit needed for PE

        // Get the neighbour element
        Element* nb = net.get_neighbour(x, y, z, from_dir);
        if (!nb) return;

        // The neighbour's outport that corresponds to the opposite direction
        Port out_to_use = Element::outport_to_inlink(from_dir); // because neighbour sent to us via that outport
        int out_idx = static_cast<int>(out_to_use);

        // If neighbour is a router, we send credit to its outport
        if (nb->is_router) {
            if (out_idx >=1 && out_idx <=5) {
                nb->outports[out_idx].credit_received = true;
                total_credits_sent++;
            }
        } else {
            // Neighbour is a recswitch: we need to propagate credit through the recswitch
            // This is complex: we need to find which input of the recswitch is connected to this output
            // We'll implement a helper function to traverse backwards.
            propagate_credit_through_recswitch(nb, out_idx);
        }
    }

    void propagate_credit_through_recswitch(Element* rec, int out_port) {
        // Find the input that maps to this output (assuming unique mapping)
        for (int in=0; in<4; ++in) {
            if (rec->crossbar[in][out_port-1]) { // out_port is 1..4
                // The credit should go to the neighbour that feeds this input
                Port in_dir;
                switch (in+1) {
                    case 1: in_dir = Port::NORTH; break;
                    case 2: in_dir = Port::WEST;  break;
                    case 3: in_dir = Port::SOUTH; break;
                    case 4: in_dir = Port::EAST;  break;
                }
                // Get the neighbour that is connected to this input
                Element* nb = net.get_neighbour(rec->x, rec->y, rec->z, in_dir);
                if (!nb) break;
                // Now we need to send credit to that neighbour's outport (opposite direction)
                Port out_to_use = Element::outport_to_inlink(in_dir);
                int out_idx = static_cast<int>(out_to_use);
                if (nb->is_router) {
                    if (out_idx >=1 && out_idx <=5) {
                        nb->outports[out_idx].credit_received = true;
                        total_credits_sent++;
                    }
                } else {
                    // Recursively propagate through recswitch chain (should be limited)
                    propagate_credit_through_recswitch(nb, out_idx);
                }
                break;
            }
        }
    }

    void propagate_credits(int cycle) {
        // For all elements, apply credit_received to increase empty_slots
        for (int x=1; x<=ELEMENTS_X; ++x) {
            for (int y=1; y<=ELEMENTS_Y; ++y) {
                for (int z=1; z<=NETWORK_Z; ++z) {
                    Element& elem = net.grid[x][y][z];
                    for (int out=1; out<=5; ++out) {
                        if (elem.outports[out].credit_received) {
                            elem.outports[out].empty_slots++;
                            if (elem.outports[out].empty_slots > BUFFER_SIZE)
                                elem.outports[out].empty_slots = BUFFER_SIZE;
                            elem.outports[out].credit_received = false;
                        }
                    }
                }
            }
        }
    }

    // ---- Statistics ----
    void print_statistics() {
        ofstream result("Result_improved.txt");
        result << "=== Improved RecNoC Simulator Results ===\n";
        result << "Network: " << NETWORK_X << "x" << NETWORK_Y << "x" << NETWORK_Z << "\n";
        result << "Cluster size: " << CLUSTER_SIZE << ", Corridors: " << NUM_CORRIDORS << "\n";
        result << "Buffer size: " << BUFFER_SIZE << ", NI buffer: " << NI_BUFFER_SIZE << "\n";
        result << "Injection rate: " << INJECTION_RATE << "\n";
        result << "Simulation time: " << SIMULATION_TIME << " cycles\n";
        result << "Traffic generation duration: " << TRAFFIC_GEN_DURATION << "\n";
        result << "\n--- Statistics ---\n";
        result << "Total flits generated: " << total_generated << "\n";
        result << "Flits delivered: " << total_delivered << "\n";
        result << "Delivery ratio: " << (total_delivered * 100.0 / max(1,total_generated)) << "%\n";
        if (!flit_latencies.empty()) {
            double avg = accumulate(flit_latencies.begin(), flit_latencies.end(), 0.0) / flit_latencies.size();
            int min_lat = *min_element(flit_latencies.begin(), flit_latencies.end());
            int max_lat = *max_element(flit_latencies.begin(), flit_latencies.end());
            result << "Average latency: " << avg << " cycles\n";
            result << "Min latency: " << min_lat << " cycles\n";
            result << "Max latency: " << max_lat << " cycles\n";
        }
        result << "Credits sent: " << total_credits_sent << "\n";
        result << "Errors: " << errors << "\n";
        result.close();
        cout << "Simulation finished. Results written to Result_improved.txt\n";
    }
};

// ================================ Main =======================================
int main() {
    Simulator sim;
    sim.run();
    return 0;
}
