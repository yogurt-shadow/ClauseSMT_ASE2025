#include <bits/stdc++.h>
#include <assert.h>
#include <sys/stat.h>
#include <dirent.h>
#include <unistd.h>
#include <stdlib.h>
#include <sys/wait.h>

using namespace std;

string instance_list_path, solver_path, output_path;
string time_limit, memory_limit;
int max_process_num;

string getPath(const string &str) {
    int start = -1, end = -1;
    for (int i = str.length() - 1; i >= 0; i--) {
        if (str[i] == '.' && end == -1) {
            end = i;
        }
        if (str[i] == '/' && start == -1) {
            start = i;
            break;
        }
    }
    return str.substr(start + 1, end - start - 1);
}

class System_Comand_Helper {
private:
    string cmd;
public:
    bool run() {
        if (system(cmd.c_str()) != 0) {
            cout << "system error: " << cmd << endl;
            return false;
        }
        return true;
    }
    void run_mkdir_cmd(const string &dir_path) {
        cmd = "mkdir -p " + dir_path;
        run();
    }
    void run_remove_cmd(const string & str) {
        cmd = "rm -r " + str;
        run();
    }
    void run_echo_string_cmd(const string &str, const string & path) {
        stringstream ss;
        ss << "echo " << str << " >>" + path;
        cmd = ss.str();
        run();
    }

    void run_touch_cmd(const string & str){
        stringstream ss;
        ss << "touch " << str;
        cmd = ss.str();
        run();
    }

    void run_z3_cmd(const string &path) {
        string rela_path = getPath(path);
        string final_path = output_path + rela_path + ".txt";
        run_touch_cmd(final_path);
        stringstream ss;
        ss << solver_path << " " << path;
        ss << " -T:" << time_limit;
        ss << " -memory:" << memory_limit;
        ss << " -st > " + final_path;
        cmd = ss.str();
        if (!run()) {
            run_echo_string_cmd("memoryout", final_path);
        }
    }
};

class Z3_Multiprocess_Runner {
private:
    System_Comand_Helper &sch;
    vector<string> &vec_job;
    unsigned ite, siz;
public:
    Z3_Multiprocess_Runner(System_Comand_Helper &_sch, vector<string> &_vec_job)
        : sch(_sch), vec_job(_vec_job), ite(0), siz(_vec_job.size()) {}

    void init() {
        ite = 0;
        siz = vec_job.size();
    }
    bool has_next_job() {
        if (ite >= siz) return false;
        return true;
    }
    unsigned get_cur_job_id() {
        return ite;
    }
    void get_next_job() {
        ++ite;
    }

    void child_process() {
        const string &job = vec_job[ite];
        stringstream ss;
        ss << "file[" << ite << "] = " << job;
        string tag = ss.str();
        sch.run_z3_cmd(job);
        cout << "finish: " << tag << endl;
        exit(0);
    }
    void process_finished_child(const unsigned &job_id, const int &sta) {
        if (sta != 0) {
            stringstream ss;
            ss << "file[" << job_id << "] = " << vec_job[job_id];
            string tag = ss.str();
            cout << "error: " << tag << endl;
        }
    }
};
template<typename T>
class Process_Pool {
private:
    unsigned max_proc_num;
    map<unsigned, pid_t> dict_proc_id;
public:
    Process_Pool(unsigned _max_proc_num = 1234567) : max_proc_num(_max_proc_num) {}
    void handle_finished_process(T &func) {
        pid_t child_pid;
        int sta;
        for (const auto x : dict_proc_id) {
            child_pid = waitpid(x.second, &sta, WNOHANG);
            if (child_pid == 0) { // child process does not finish
                // do nothing
            }
            else { // child process finished
                // assert(child_pid == x.second);
                func.process_finished_child(x.first, sta);
                dict_proc_id.erase(x.first);
                break;
            }
        }
    }
    void solve(T &func) {
        bool is_parent;
        func.init();
        while (true) {
            is_parent = false;
            if (!func.has_next_job())
                break;
            pid_t pid = fork();
            if (pid == -1) {
                cout << "fork failed" << endl;
                exit(1);
            }
            if(pid == 0) {
                func.child_process();
                exit(0);
            }
            else {
                unsigned job_id = func.get_cur_job_id();
                dict_proc_id[job_id] = pid;
                is_parent = true;
                while (dict_proc_id.size() >= max_proc_num) {
                    handle_finished_process(func);
                }
            }
            func.get_next_job();
        }
        if (!is_parent) return ;
        while (!dict_proc_id.empty()) {
            handle_finished_process(func);
        }
    }
};

void get_jobs(System_Comand_Helper &sch, vector<string> &vec_job) {

    ifstream ifs(instance_list_path);
    string word;
    while (ifs >> word) {
        vec_job.emplace_back(word);
    }
}
template<typename T>
void shuffle_jobs(T &vec) {
    mt19937 mt(123);
    shuffle(vec.begin(), vec.end(), mt);
}
void solve() {
    System_Comand_Helper sch;
    vector<string> vec_job;
    get_jobs(sch, vec_job);
    shuffle_jobs(vec_job);
    cout << "vec file size: " << vec_job.size() << endl;
    Process_Pool<Z3_Multiprocess_Runner> pp(max_process_num);
    Z3_Multiprocess_Runner z3mr(sch, vec_job);
    pp.solve(z3mr);
}

int main(int argc, char **argv) {
    if(argc != 7) {
        cout << "Usage: ./parallel_run [instance_list_path] [solver_path] [output_path] [time_limit] [memory_limit] [max_process_num]" << endl;
        return 1;
    }
    instance_list_path = argv[1];
    solver_path = argv[2];
    output_path = argv[3];
    time_limit = argv[4];
    memory_limit = argv[5];
    max_process_num = atoi(argv[6]);
    struct stat st;
    if (stat(output_path.c_str(), &st) == -1) {
        cout << "mkdir " << output_path << endl;
        mkdir(output_path.c_str(), 0700);
    }
    solve();
    return 0;
}
