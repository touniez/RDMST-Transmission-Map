# Anthony Zheng
m
from typing import Tuple
from collections import *
from copy import *

def reverse_digraph_representation(graph: dict) -> dict:
    """
    Modifies the inputted graph into the reversed representation, where nodes' neighbor dictionaries indicate
    incoming edges if the input had neighbor dictionaries indicating outgoing edges

    Arguments:
        graph: a dictionary of the standard representation of the graph

    Returns:
        a dictionary of a copied version of graph, but in the reversed representation
    """
    reverse = {node: {} for node in graph}
    for node1 in graph:
        for node2 in graph:
            if node1 in graph[node2].keys():
                reverse[node1][node2] = graph[node2][node1]
    return reverse

def modify_edge_weights(rgraph: dict, root: int) -> None:
    """
    Modifies edge weights of inputted graph based on Lemma 2 in the description document, where the new incoming edge
    weights are the original incoming weights minus the minimum incoming weight for each node

    Arguments:
        rgraph: a dictionary of the reversed representation of graph
        root: the root node of the graph

    Returns:
        None, the input graph is modified directly
    """
    for node1 in rgraph:
        if node1 == root:
            continue
        if len(rgraph[node1].values()) != 0:
            minimum = min(list(rgraph[node1].values()))
            for node2 in rgraph[node1]:
                rgraph[node1][node2] = rgraph[node1][node2] - minimum
    return

def compute_rdst_candidate(rgraph: dict, root: int) -> dict:
    """
    Computes a potential rdst candidate by removing all incoming edges that have weights greater than the minimum,
    such that only one edge is going into each node

    Arguments:
        rgraph: a dictionary of the reversed representation of graph, with modified edge weights
        root: the root node of the graph

    Returns:
        An RDMST or cycle, based on Lemma 1
    """
    rrgraph = deepcopy(rgraph)
    # print(rgraph)
    for node1 in rrgraph:
        if node1 == root:
            rrgraph[node1].clear()
            continue
        keys, vals = list(rrgraph[node1].keys()), list(rrgraph[node1].values())
        if len(vals) > 0:
            minimum = min(vals)
            rrgraph[node1] = {keys[vals.index(minimum)]: minimum}
    return rrgraph

def compute_cycle(rdst_candidate: dict) -> tuple:
    """
        Finds a cycle in the graph rdst_candidate

        Arguments:
            rdst_candidate: a dictionary representing a graph with only minimum incoming edges kept, based on
            Lemma 1

        Returns:
            A tuple representing the path of a cycle in the inputted rdst_candidate graph
        """
    unexplorednodes = list(rdst_candidate.keys())
    cyclepath = ()
    while len(unexplorednodes) > 0:
        currentnode = unexplorednodes[0]
        # print(currentnode)
        path = [currentnode]
        while len(path) > 0:
            if path[-1] not in unexplorednodes:  # if the parent was explored alread, we can skip this node
                path.clear()
                continue
            unexplorednodes.remove(path[-1])
            if rdst_candidate[path[-1]]:
                parent = list(rdst_candidate[path[-1]].keys())[0]
                if parent in path:
                    path = path[path.index(parent):]
                    cyclepath = tuple(path)
                    return cyclepath
                path.append(parent)
            else:
                path.clear()
    return cyclepath

def contract_cycle(graph: dict, cycle: tuple) -> Tuple[dict, int]:
    """
    Contracts the cycle in graph into one node, keeping all incoming edges and outgoing edges,
    but removing parallels edges and keeping the smallest weights

    Arguments:
        graph: a dictionary of the standard representation of the graph
        cycle: a tuple of nodes that are present in the cycle found in graph

    Return:
        A dictionary of the new graph with a new node added to replace cycle, and the number of the new node
    """
    mininnode = {}
    minoutnode = {}
    newnode = max(list(graph.keys())) + 1
    graph[newnode] = {}
    for node1 in graph:
        if node1 in cycle:
            continue
        for cycleNode in cycle:
            if cycleNode in graph[node1]:
                if node1 not in mininnode:
                    mininnode[node1] = []
                mininnode[node1].append(graph[node1][cycleNode])
                graph[node1].pop(cycleNode)
    for cycleNode in cycle:
        for node2 in graph[cycleNode]:
            if node2 in cycle:
                continue
            if node2 not in minoutnode:
                minoutnode[node2] = []
            minoutnode[node2].append(graph[cycleNode][node2])
        graph.pop(cycleNode)
    if len(mininnode) > 0:
        for node in mininnode:
            graph[node][newnode] = min(mininnode[node])
    if len(minoutnode) > 0:
        for node in minoutnode:
            graph[newnode][node] = min(minoutnode[node])
    return (graph, newnode)

def expand_graph(graph: dict, rdst_candidate: dict, cycle: tuple, cstar: int) -> dict:
    """
    Rebuilds the rdst candidate graph by adding back nodes that were in a cycle that have been contracted, and
    only the least weight edges are added back between cycle nodes as well as the minimum
    incoming or outgoing edges of the cycle

    Arguments:
        graph: a dictionary of the standard representation of the graph
        rdst_candidate: a reversed representation of the graph, with a contracted cycle and cstar node
        cycle: a tuple of nodes that are present in the cycle found in graph
        cstar: the label of the node that replaced

    Returns:
        a dictionary in the standard representation of the graph with the node cstar replaced with the cycle
        and all necessary edges added back
    """
    outnode = []
    innode = []
    if len(list(rdst_candidate[cstar].keys())) > 0:
        outnode = [node for node in list(rdst_candidate[cstar].keys())]
    for node in rdst_candidate:
        if node is cstar:
            continue
        if cstar in list(rdst_candidate[node].keys()):
            innode.append(node)
            rdst_candidate[node].pop(cstar)
    rdst_candidate.pop(cstar)
    for node in cycle:
        rdst_candidate[node] = {}
    startcycle = None
    if len(innode) > 0:
        for inn in range(len(innode)):
            minin = []
            mininnodes = []
            for connection in list(graph[innode[inn]].keys()):
                if connection not in cycle:
                    continue
                mininnodes.append(connection)
                minin.append(graph[innode[inn]][connection])
            mininedge = min(minin)
            rdst_candidate[innode[inn]][mininnodes[minin.index(mininedge)]] = mininedge
            startcycle = cycle.index(mininnodes[minin.index(mininedge)])
    if len(outnode) > 0:
        for out in range(len(outnode)):
            found = False
            outmin = []
            for cycleelement in cycle:
                for connection in graph[cycleelement]:
                    if connection in cycle:
                        continue
                    if connection == outnode[out]:
                        outmin.append(graph[cycleelement][connection])
            minoutedge = min(outmin)
            for cycleelement in cycle:
                if outnode[out] in graph[cycleelement]:
                    if graph[cycleelement][outnode[out]] == minoutedge and not found:
                        rdst_candidate[cycleelement][outnode[out]] = graph[cycleelement][outnode[out]]
                        found = True
    if startcycle == None:
        for index in range(len(cycle)):
            cindex = (index) % len(cycle)
            nindex = (index - 1) % len(cycle)
            rdst_candidate[cycle[cindex]][cycle[nindex]] = graph[cycle[cindex]][cycle[nindex]]
    else:
        for index in range(len(cycle) - 1):
            cindex = (startcycle - index) % len(cycle)
            nindex = (startcycle - index - 1) % len(cycle)
            rdst_candidate[cycle[cindex]][cycle[nindex]] = graph[cycle[cindex]][cycle[nindex]]
    return rdst_candidate

def bfs(graph, startnode):
    """
        Perform a breadth-first search on digraph graph starting at node startnode.

        Arguments:
        graph -- directed graph
        startnode - node in graph to start the search from

        Returns:
        The distances from startnode to each node
    """
    dist = {}

    # Initialize distances
    for node in graph:
        dist[node] = float('inf')
    dist[startnode] = 0

    # Initialize search queue
    queue = deque([startnode])

    # Loop until all connected nodes have been explored
    while queue:
        node = queue.popleft()
        for nbr in graph[node]:
            if dist[nbr] == float('inf'):
                dist[nbr] = dist[node] + 1
                queue.append(nbr)
    return dist

def compute_rdmst(graph, root):
    """
        This function checks if:
        (1) root is a node in digraph graph, and
        (2) every node, other than root, is reachable from root
        If both conditions are satisfied, it calls compute_rdmst_helper
        on (graph, root).

        Since compute_rdmst_helper modifies the edge weights as it computes,
        this function reassigns the original weights to the RDMST.

        Arguments:
        graph -- a weighted digraph in standard dictionary representation.
        root -- a node id.

        Returns:
        An RDMST of graph rooted at r and its weight, if one exists;
        otherwise, nothing.
    """

    if root not in graph:
        print("The root node does not exist")
        return

    distances = bfs(graph, root)
    for node in graph:
        if distances[node] == float('inf'):
            print("The root does not reach every other node in the graph")
            return

    rdmst = compute_rdmst_helper(graph, root)

    # reassign the original edge weights to the RDMST and computes the total
    # weight of the RDMST
    rdmst_weight = 0
    for node in rdmst:
        for nbr in rdmst[node]:
            rdmst[node][nbr] = graph[node][nbr]
            rdmst_weight += rdmst[node][nbr]

    return (rdmst, rdmst_weight)

def compute_rdmst_helper(graph, root):
    """
        Computes the RDMST of a weighted digraph rooted at node root.
        It is assumed that:
        (1) root is a node in graph, and
        (2) every other node in graph is reachable from root.

        Arguments:
        graph -- a weighted digraph in standard dictionary representation.
        root -- a node in graph.

        Returns:
        An RDMST of graph rooted at root. The weights of the RDMST
        do not have to be the original weights.
        """

    # reverse the representation of graph
    rgraph = reverse_digraph_representation(graph)
    # print("rgraph: " + str(rgraph))

    # Step 1 of the algorithm
    modify_edge_weights(rgraph, root)
    # print("modified: " + str(rgraph))

    # Step 2 of the algorithm
    rdst_candidate = compute_rdst_candidate(rgraph, root)
    # print("rdst cand: " + str(rdst_candidate))

    # compute a cycle in rdst_candidate
    cycle = compute_cycle(rdst_candidate)
    # print("cycle: "  +str(cycle))

    # Step 3 of the algorithm
    if not cycle:
        return reverse_digraph_representation(rdst_candidate)
    else:
        # Step 4 of the algorithm
        # print("rgraph 2:  " + str(rgraph))
        g_copy = deepcopy(rgraph)
        g_copy = reverse_digraph_representation(g_copy)
        # print("gcopy: " + str(g_copy))
        # Step 4(a) of the algorithm
        (contracted_g, cstar) = contract_cycle(g_copy, cycle)
        # print("contracted g: "  + str(contracted_g))
        # print("cstar" + str(cstar))
        # cstar = max(contracted_g.keys())

        # Step 4(b) of the algorithm
        # print(contracted_g)
        new_rdst_candidate = compute_rdmst_helper(contracted_g, root)
        # print(new_rdst_candidate)

        # Step 4(c) of the algorithm
        # print(reverse_digraph_representation(rgraph))
        # print(new_rdst_candidate)
        # print(cycle)
        # print(cstar)
        rdmst = expand_graph(reverse_digraph_representation(rgraph), new_rdst_candidate, cycle, cstar)

        return rdmst

###### PART 4 #######

def infer_transmap(gen_data, epi_data, patient_id):
    """
        Infers a transmission map based on genetic
        and epidemiological data rooted at patient_id

        Arguments:
        gen_data -- filename with genetic data for each patient
        epi_data -- filename with epidemiological data for each patient
        patient_id -- the id of the 'patient 0'

        Returns:
        The most likely transmission map for the given scenario as the RDMST
        of a weighted, directed, complete digraph
        """

    complete_digraph = construct_complete_weighted_digraph(gen_data, epi_data)
    return compute_rdmst(complete_digraph, patient_id)

def read_patient_sequences(filename):
    """
        Turns the bacterial DNA sequences (obtained from patients) into a list containing tuples of
        (patient ID, sequence).

        Arguments:
        filename -- the input file containing the sequences

        Returns:
        A list of (patient ID, sequence) tuples.
        """
    sequences = []
    with open(filename) as f:
        line_num = 0
        for line in f:
            if len(line) > 5:
                patient_num, sequence = line.split("\t")
                sequences.append((int(patient_num), ''.join(e for e in sequence if e.isalnum())))
    return sequences

def read_patient_traces(filename):
    """
        Reads the epidemiological data file and computes the pairwise epidemiological distances between patients

        Arguments:
        filename -- the input file containing the sequences

        Returns:
        A dictionary of dictionaries where dict[i][j] is the
        epidemiological distance between i and j.
    """
    trace_data = []
    patient_ids = []
    first_line = True
    with open(filename) as f:
        for line in f:
            if first_line:
                patient_ids = line.split()
                patient_ids = list(map(int, patient_ids))
                first_line = False
            elif len(line) > 5:
                trace_data.append(line.rstrip('\n'))
    return compute_pairwise_epi_distances(trace_data, patient_ids)

def compute_pairwise_gen_distances(sequences, distance_function):
    """
        Computes the pairwise genetic distances between patients (patients' isolate genomes)

        Arguments:
        sequences -- a list of sequences that correspond with patient id's
        distance_function -- the distance function to apply to compute the weight of the
        edges in the returned graph

        Returns:
        A dictionary of dictionaries where gdist[i][j] is the
        genetic distance between i and j.
        """
    gdist = {}
    cultures = {}

    # Count the number of differences of each sequence
    for i in range(len(sequences)):
        patient_id = sequences[i][0]
        seq = sequences[i][1]
        if patient_id in cultures:
            cultures[patient_id].append(seq)
        else:
            cultures[patient_id] = [seq]
            gdist[patient_id] = {}
    # Add the minimum sequence score to the graph
    for pat1 in range(1, max(cultures.keys()) + 1):
        for pat2 in range(pat1 + 1, max(cultures.keys()) + 1):
            min_score = float("inf")
            for seq1 in cultures[pat1]:
                for seq2 in cultures[pat2]:
                    score = distance_function(seq1, seq2)
                    if score < min_score:
                        min_score = score
            gdist[pat1][pat2] = min_score
            gdist[pat2][pat1] = min_score
    return gdist

### HELPER FUNCTIONS. ###

def find_first_positives(trace_data):
    """
        Finds the first positive test date of each patient
        in the trace data.
        Arguments:
        trace_data -- a list of data pertaining to location
        and first positive test date
        Returns:
        A dictionary with patient id's as keys and first positive
        test date as values. The date numbering starts from 0 and
        the patient numbering starts from 1.
        """
    first_pos = {}
    for pat in range(len(trace_data[0])):
        first_pos[pat + 1] = None
        for date in range(len(trace_data)):
            if trace_data[date][pat].endswith(".5"):
                first_pos[pat + 1] = date
                break
    return first_pos

def compute_epi_distance(pid1, pid2, trace_data, first_pos1, first_pos2, patient_ids):
    """
        Computes the epidemiological distance between two patients.

        Arguments:
        pid1 -- the assumed donor's index in trace data
        pid2 -- the assumed recipient's index in trace data
        trace_data -- data for days of overlap and first positive cultures
        first_pos1 -- the first positive test day for pid1
        first_pos2 -- the first positive test day for pid2
        patient_ids -- an ordered list of the patient IDs given in the text file

        Returns:
        Finds the epidemiological distance from patient 1 to
        patient 2.
        """
    first_overlap = -1
    assumed_trans_date = -1
    pid1 = patient_ids.index(pid1)
    pid2 = patient_ids.index(pid2)
    # Find the first overlap of the two patients
    for day in range(len(trace_data)):
        if (trace_data[day][pid1] == trace_data[day][pid2]) & \
                (trace_data[day][pid1] != "0"):
            first_overlap = day
            break
    if (first_pos2 < first_overlap) | (first_overlap < 0):
        return len(trace_data) * 2 + 1
    # Find the assumed transmission date from patient 1 to patient 2
    for day in range(first_pos2, -1, -1):
        if (trace_data[day][pid1] == trace_data[day][pid2]) & \
                (trace_data[day][pid1] != "0"):
            assumed_trans_date = day
            break
    sc_recip = first_pos2 - assumed_trans_date

    if first_pos1 < assumed_trans_date:
        sc_donor = 0
    else:
        sc_donor = first_pos1 - assumed_trans_date
    return sc_donor + sc_recip

def compute_pairwise_epi_distances(trace_data, patient_ids):
    """
        Turns the patient trace data into a dictionary of pairwise
        epidemiological distances.

        Arguments:
        trace_data -- a list of strings with patient trace data
        patient_ids -- ordered list of patient IDs to expect

        Returns:
        A dictionary of dictionaries where edist[i][j] is the
        epidemiological distance between i and j.
        """
    edist = {}
    proc_data = []
    # Reformat the trace data
    for i in range(len(trace_data)):
        temp = trace_data[i].split()[::-1]
        proc_data.append(temp)
    # Find first positive test days and remove the indication from the data
    first_pos = find_first_positives(proc_data)
    for pid in first_pos:
        day = first_pos[pid]
        proc_data[day][pid - 1] = proc_data[day][pid - 1].replace(".5", "")
    # Find the epidemiological distance between the two patients and add it
    # to the graph
    for pid1 in patient_ids:
        edist[pid1] = {}
        for pid2 in patient_ids:
            if pid1 != pid2:
                epi_dist = compute_epi_distance(pid1, pid2, proc_data,
                                                first_pos[pid1], first_pos[pid2], patient_ids)
                edist[pid1][pid2] = epi_dist
    return edist

### MY FUNCTIONS. ###

def compute_genetic_distance(list1, list2):
    """
    Computes the hamming distance between the two inpuuted sequences

    Arguments:
         list1: the first sequence to be compared
         list2: the second sequence to be compared

    Returns:
        An integer representing the hamming distance of the two inputted sequences
    """
    list3 = zip(list1, list2)
    dist = 0
    for element in list3:
        if element[0] != element[1]:
            dist = dist + 1
    return dist

def construct_complete_weighted_digraph(gen_data, epi_data):
    """
    Generates a completely connected graph representing the genetic-epidemiological distances between every
    patient and each of the others

    Arguments:
        gen_data: the genetic data of every patient
        epi_data: the epidemiological data of every patient

    Returns:
        A complete graph with patients as nodes and their genetic-epidemiological distances as edges
    """
    patient_sequences = read_patient_sequences(gen_data)
    patient_epi = read_patient_traces(epi_data)
    trace_graph = {}
    max_dist = 0
    for patient in patient_epi:
        if max(list(patient_epi[patient].values())) > max_dist:
            max_dist = max(list(patient_epi[patient].values()))
    gendist = compute_pairwise_gen_distances(patient_sequences, compute_genetic_distance)
    for patient in patient_sequences:
        trace_graph[patient[0]] = {}
        for other_patient in patient_sequences:
            if other_patient is patient:
                continue
            trace_graph[patient[0]][other_patient[0]] = gendist[patient[0]][other_patient[0]] + \
                999/10**5 * (patient_epi[patient[0]][other_patient[0]]/max_dist)
    return trace_graph

#print(construct_complete_weighted_digraph("patient_sequences.txt", "patient_traces.txt"))

#transmission map
#print(infer_transmap("patient_sequences.txt", "patient_traces.txt", 1))

#test cases
#print(reverse_digraph_representation({0 : {1: 15}, 1: {}, 2: {1: 10}, 3: {1: 20}}))
#print(compute_rdst_candidate({0: {}, 1: {0: 3, 2: 0, 3: 4}, 2: {0: 0, 1: 0, 3: 4}, 3: {}}, 0))
#print(compute_cycle({1 : {}, 2: {1:1}, 3: {2: 2}, 4: {2:3}, 5: {7: 2}, 6: {5: 2}, 7: {6: 1}}))
#print(contract_cycle({1 : {2: 1, 5: 2}, 2: {3:1, 4: 2}, 3: {}, 4: {}, 5: {7: 2}, 6: {5: 2}, 7: {6: 1, 8: 3}}, (5, 6, 7)))
#print(contract_cycle({1: {2: 20, 3: 4, 4: 20}, 2: {3: 2, 6: 16}, 3: {4: 8, 5: 20}, 4: {5: 4, 6: 8}, 5: {2: 4}, 6: {}}, (2, 3, 4, 5)))
#print(contract_cycle({1: {2: 2}, 2: {3: 2}, 3: {1: 2}}, (1,2,3)))
#print(contract_cycle({0:{1:0}, 1:{2:0}, 2:{2:0, 1:0}}, (1, 2)))
#print(expand_graph({1: {2: 6}, 2: {3: 7, 4: 2}, 3: {1: 5, 4: 4}, 4: {}}, {5: {4: 2}, 4: {}}, (3, 2, 1), 5))
#print(expand_graph({0: {1: 3, 2: 4, 3: 3}, 1: {2: 3, 3: 2}, 2: {3: 4, 1: 2}, 3: {1: 5, 2: 4}}, {0: {4: 3}, 4: {}}, (1, 2, 3), 4))